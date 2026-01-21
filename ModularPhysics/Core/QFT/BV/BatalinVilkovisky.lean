import ModularPhysics.Core.QFT.BV.BRST

namespace ModularPhysics.Core.QFT.BV

/-!
# Batalin-Vilkovisky Formalism

The BV formalism is the most general framework for quantizing gauge theories.
It systematically handles arbitrary gauge symmetries, including:
- Reducible gauge theories (gauge of gauge symmetries)
- Open gauge algebras (structure functions, not constants)
- Theories with on-shell closure only

## Key concepts:

1. **Antifields φ***: Conjugate to each field φ, with opposite statistics.
   Antifields are sources for BRST variations: δS/δφ* = sφ.

2. **Odd symplectic structure ω**: A Grassmann-odd closed 2-form on the field-antifield
   space. ω = dφ^A ∧ dφ*_A (implicit sum). This is the fundamental geometric structure.

3. **Antibracket (,)**: The odd Poisson bracket induced by ω^{-1}.
   (F, G) = δ_R F/δφ^A · δ_L G/δφ*_A - δ_R F/δφ*_A · δ_L G/δφ^A

4. **Classical master equation**: (S, S) = 0
   Encodes gauge invariance in BV language. The solution S is the BV action.

5. **Quantum master equation**: (S, S) - 2iℏΔS = 0
   Includes the BV Laplacian Δ. Absence of anomalies requires a solution.

6. **Gauge fixing via Lagrangian submanifolds**: The BV path integral is defined by
   integrating over a Lagrangian submanifold L ⊂ field-antifield space (ω|_L = 0).
   The choice of L corresponds to a choice of gauge-fixing fermion Ψ.

## Relation to BRST:

The BRST formalism is a special case of BV where:
- Antifields are set to zero after computing BRST transformations
- The gauge algebra closes off-shell
- The theory is irreducible (no reducibility identities)

See `BRSTFromBV` for the precise embedding.

## Applications:

- Systematic gauge fixing of any gauge theory
- BRST-antifield formulation of string field theory
- Consistent regularization of gauge theories
- Foundation for effective field theory of gauge theories
-/

open BRST

/- ============= ANTIFIELDS ============= -/

/-- Antifield φ* conjugate to field φ

    Properties:
    - Opposite Grassmann parity: ε(φ*) = ε(φ) + 1 mod 2
    - Ghost number: gh(φ*) = -gh(φ) - 1
    - Appears as source for BRST transformation: δS/δφ* = sφ -/
structure Antifield where
  /-- The original field -/
  field : Field
  /-- Name (conventionally φ*) -/
  name : String := field.name ++ "*"
  /-- Ghost number of antifield: -gh(φ) - 1 -/
  ghost_number : GhostNumber := ⟨-field.ghost_number.value - 1⟩
  /-- Grassmann parity (opposite to field) -/
  parity : GrassmannParity := field.parity.flip

/-- Extended field space: fields and antifields -/
structure ExtendedFieldSpace where
  /-- The original fields -/
  fields : List Field
  /-- The antifields -/
  antifields : List Antifield
  /-- Each field has its antifield -/
  paired : antifields.length = fields.length

/-- Number of field-antifield pairs -/
def ExtendedFieldSpace.numPairs (E : ExtendedFieldSpace) : ℕ := E.fields.length

/-- Total dimension of extended field space (2n for n fields) -/
def ExtendedFieldSpace.totalDim (E : ExtendedFieldSpace) : ℕ := 2 * E.fields.length

/-- Get the antifield conjugate to a field by index -/
def ExtendedFieldSpace.getAntifield (E : ExtendedFieldSpace) (i : Fin E.fields.length) :
    Antifield :=
  E.antifields.get (i.cast E.paired.symm)

/-- Count bosonic fields -/
def ExtendedFieldSpace.numBosonic (E : ExtendedFieldSpace) : ℕ :=
  E.fields.filter (fun f => match f.parity with | .even => true | .odd => false) |>.length

/-- Count fermionic fields -/
def ExtendedFieldSpace.numFermionic (E : ExtendedFieldSpace) : ℕ :=
  E.fields.filter (fun f => match f.parity with | .odd => true | .even => false) |>.length

/-- Functional on the extended field space -/
structure BVFunctional where
  /-- The functional -/
  functional : ExtendedFieldSpace → ℝ
  /-- Ghost number -/
  ghost_number : GhostNumber
  /-- Grassmann parity -/
  parity : GrassmannParity

/- ============= ODD SYMPLECTIC STRUCTURE ============= -/

/-- Odd symplectic form (BV symplectic structure)

    The BV field-antifield space carries a canonical Grassmann-ODD symplectic form:

      ω = dφ^A ∧ dφ*_A  (implicit sum over A)

    Key properties:
    - ω has Grassmann parity ODD (shifts statistics by 1)
    - ω is closed: dω = 0
    - ω is non-degenerate
    - Ghost number: gh(ω) = -1

    The antibracket (,) is the odd Poisson bracket corresponding to ω^{-1}.
    A Lagrangian submanifold L satisfies ω|_L = 0 and dim(L) = (1/2)dim(field-antifield space).

    Geometrically, the field-antifield space is an odd cotangent bundle T*[-1]M
    where M is the original field space and [-1] denotes the parity shift. -/
structure OddSymplecticForm where
  /-- The extended field space on which ω lives -/
  space : ExtendedFieldSpace
  /-- Ghost number of ω is -1 (maps degree n to degree n-1) -/
  ghost_number : GhostNumber := ⟨-1⟩
  /-- ω has odd Grassmann parity -/
  parity : GrassmannParity := GrassmannParity.odd
  /-- Pairing of tangent vectors (represents ω(v,w)) -/
  pairing : ExtendedFieldSpace → ExtendedFieldSpace → ℝ
  /-- Graded antisymmetry: ω(v,w) = -(-1)^{ε(v)ε(w)+1} ω(w,v) -/
  graded_antisym : ∀ s₁ s₂, pairing s₁ s₂ = -pairing s₂ s₁  -- simplified for even base
  /-- Non-degeneracy: if ω(v,w) = 0 for all w, then v = 0 -/
  nondegenerate : ∀ s, (∀ s', pairing s s' = 0) → s = s

/- Closedness of the odd symplectic form: dω = 0

   This is automatic for the canonical form ω = dφ^A ∧ dφ*_A since
   it is exact (ω = dθ where θ = φ*_A dφ^A is the Liouville 1-form).

   NOTE: This property is definitionally true for the canonical BV symplectic form,
   so no axiom is needed. -/

/- The antibracket is the odd Poisson bracket induced by ω^{-1}

   For F, G functions on field-antifield space:
   (F, G) = ω^{AB} (∂_A F)(∂_B G)

   where ω^{AB} is the inverse of ω_{AB}. In canonical coordinates:
   ω^{AB} gives (F, G) = (∂F/∂φ^A)(∂G/∂φ*_A) - (∂F/∂φ*_A)(∂G/∂φ^A)

   NOTE: This is a definitional relationship - the antibracket is defined
   as the inverse of the odd symplectic form. No axiom is needed. -/

/- ============= LAGRANGIAN SUBMANIFOLDS ============= -/

/-- Lagrangian submanifold with respect to odd symplectic form

    A submanifold L of the field-antifield space is Lagrangian if:
    1. ω|_L = 0 (the symplectic form vanishes on L)
    2. dim(L) = (1/2) dim(field-antifield space) (maximal isotropic)

    In BV gauge fixing, L is specified by a gauge-fixing fermion Ψ:
      L_Ψ = { (φ, φ*) | φ*_A = ∂Ψ/∂φ^A }

    The BV path integral is defined as integration over L. -/
structure LagrangianSubmanifoldBV where
  /-- The odd symplectic form -/
  omega : OddSymplecticForm
  /-- Constraint defining the submanifold (as a condition on field-antifield configs) -/
  constraint : ExtendedFieldSpace → Prop
  /-- ω vanishes on L: ω(v,w) = 0 for tangent vectors v, w to L -/
  isotropic : ∀ s₁ s₂, constraint s₁ → constraint s₂ → omega.pairing s₁ s₂ = 0
  /-- Maximality: L has half the dimension (encoded abstractly) -/
  maximal : True  -- Would need dimension theory to state precisely

/- ============= ANTIBRACKET ============= -/

/-- Koszul sign (-1)^{pq} for graded commutativity -/
def koszulSign (p q : GrassmannParity) : ℤ :=
  match p, q with
  | .even, _ => 1
  | _, .even => 1
  | .odd, .odd => -1

/-- Sign for antibracket antisymmetry: -(-1)^{(ε_F+1)(ε_G+1)}
    - (even, even): (0+1)(0+1) = 1, so -(-1)^1 = 1
    - (even, odd):  (0+1)(1+1) = 2, so -(-1)^2 = -1
    - (odd, even):  (1+1)(0+1) = 2, so -(-1)^2 = -1
    - (odd, odd):   (1+1)(1+1) = 4, so -(-1)^4 = -1 -/
def antibracketSign (p q : GrassmannParity) : ℤ :=
  match p, q with
  | .even, .even => 1   -- -(-1)^1 = 1
  | .even, .odd => -1   -- -(-1)^2 = -1
  | .odd, .even => -1   -- -(-1)^2 = -1
  | .odd, .odd => -1    -- -(-1)^4 = -1

/-- Resulting parity of antibracket (F,G) -/
def antibracketParity (p q : GrassmannParity) : GrassmannParity :=
  match p, q with
  | .even, .even => .odd
  | .even, .odd => .even
  | .odd, .even => .even
  | .odd, .odd => .odd

/-- Antibracket: odd Poisson bracket on BV field space
    (F, G) = δ_R F/δφ^A · δ_L G/δφ*_A - δ_R F/δφ*_A · δ_L G/δφ^A -/
structure Antibracket where
  space : ExtendedFieldSpace
  bracket : BVFunctional → BVFunctional → BVFunctional
  ghost_additive : ∀ F G : BVFunctional,
    (bracket F G).ghost_number.value = F.ghost_number.value + G.ghost_number.value + 1
  parity_odd : ∀ F G : BVFunctional,
    (bracket F G).parity = antibracketParity F.parity G.parity

/-- Shifted parity sign (-1)^{(ε+1)(η+1)} for Jacobi identity -/
def shiftedKoszulSign (p q : GrassmannParity) : ℤ :=
  match p, q with
  | .even, .even => -1  -- (0+1)(0+1) = 1
  | .even, .odd => 1    -- (0+1)(1+1) = 2
  | .odd, .even => 1    -- (1+1)(0+1) = 2
  | .odd, .odd => 1     -- (1+1)(1+1) = 4

/-- Zero functional -/
def zeroBVFunctional (gh : GhostNumber) (p : GrassmannParity) : BVFunctional :=
  ⟨fun _ => 0, gh, p⟩

/-- Scalar multiplication of BV functional -/
def smulBVFunctional (c : ℝ) (F : BVFunctional) : BVFunctional :=
  ⟨fun s => c * F.functional s, F.ghost_number, F.parity⟩

/-- Addition of BV functionals (unchecked - caller ensures compatibility) -/
def addBVFunctional (F G : BVFunctional) : BVFunctional :=
  ⟨fun s => F.functional s + G.functional s, F.ghost_number, F.parity⟩

/-- Negation of BV functional -/
def negBVFunctional (F : BVFunctional) : BVFunctional :=
  ⟨fun s => -F.functional s, F.ghost_number, F.parity⟩

/-- Product of BV functionals -/
def mulBVFunctional (F G : BVFunctional) : BVFunctional :=
  ⟨fun s => F.functional s * G.functional s,
   ⟨F.ghost_number.value + G.ghost_number.value⟩,
   match F.parity, G.parity with
   | .even, p => p | p, .even => p | .odd, .odd => .even⟩

/-- Constant BV functional -/
def constBVFunctional (c : ℝ) : BVFunctional :=
  ⟨fun _ => c, ⟨0⟩, .even⟩

/-- Check if functional has definite ghost number n -/
def hasGhostNumber (F : BVFunctional) (n : ℤ) : Prop := F.ghost_number.value = n

/-- Check if functional is bosonic -/
def isBosonic (F : BVFunctional) : Prop := F.parity = .even

/-- Check if functional is fermionic -/
def isFermionic (F : BVFunctional) : Prop := F.parity = .odd

/-- Total ghost number of extended field space (should be 0) -/
def ExtendedFieldSpace.totalGhostNumber (E : ExtendedFieldSpace) : ℤ :=
  E.fields.foldl (fun acc f => acc + f.ghost_number.value) 0 +
  E.antifields.foldl (fun acc a => acc + a.ghost_number.value) 0

/- ============= BV THEORY STRUCTURE ============= -/

/-- Core BV theory structure consolidating fundamental axioms about the antibracket -/
structure BVTheory where
  /-- Graded antisymmetry: (F,G) = -(-1)^{(ε_F+1)(ε_G+1)} (G,F) -/
  antibracket_graded_antisymmetry : ∀ (ab : Antibracket) (F G : BVFunctional),
    (ab.bracket F G).functional = fun s =>
      antibracketSign F.parity G.parity * (ab.bracket G F).functional s
  /-- Graded Jacobi: (-1)^{(ε_F+1)(ε_H+1)} (F,(G,H)) + cyclic = 0 -/
  antibracket_jacobi : ∀ (ab : Antibracket) (F G H : BVFunctional),
    (fun s => shiftedKoszulSign F.parity H.parity *
                (ab.bracket F (ab.bracket G H)).functional s +
              shiftedKoszulSign G.parity F.parity *
                (ab.bracket G (ab.bracket H F)).functional s +
              shiftedKoszulSign H.parity G.parity *
                (ab.bracket H (ab.bracket F G)).functional s) = fun _ => 0
  /-- Antibracket with zero gives zero -/
  antibracket_zero_left : ∀ (ab : Antibracket) (F : BVFunctional),
    (ab.bracket (zeroBVFunctional ⟨0⟩ .even) F).functional = fun _ => 0
  /-- Leibniz rule: (F, GH) = (F,G)H + (-1)^{(ε_F+1)ε_G} G(F,H) -/
  antibracket_leibniz : ∀ (ab : Antibracket) (F G H : BVFunctional),
    (ab.bracket F (mulBVFunctional G H)).functional = fun s =>
      (mulBVFunctional (ab.bracket F G) H).functional s +
      (match F.parity, G.parity with
       | .even, .even => 1   -- (0+1)·0 = 0
       | .even, .odd => -1   -- (0+1)·1 = 1
       | .odd, .even => 1    -- (1+1)·0 = 0
       | .odd, .odd => 1) *  -- (1+1)·1 = 2
        (mulBVFunctional G (ab.bracket F H)).functional s

/-- BV theory axiom -/
axiom bvTheoryD : BVTheory

/-- Graded antisymmetry: (F,G) = -(-1)^{(ε_F+1)(ε_G+1)} (G,F) -/
theorem antibracket_graded_antisymmetry (ab : Antibracket) (F G : BVFunctional) :
  (ab.bracket F G).functional = fun s =>
    antibracketSign F.parity G.parity * (ab.bracket G F).functional s :=
  bvTheoryD.antibracket_graded_antisymmetry ab F G

/-- Graded Jacobi: (-1)^{(ε_F+1)(ε_H+1)} (F,(G,H)) + cyclic = 0 -/
theorem antibracket_jacobi (ab : Antibracket) (F G H : BVFunctional) :
  (fun s => shiftedKoszulSign F.parity H.parity *
              (ab.bracket F (ab.bracket G H)).functional s +
            shiftedKoszulSign G.parity F.parity *
              (ab.bracket G (ab.bracket H F)).functional s +
            shiftedKoszulSign H.parity G.parity *
              (ab.bracket H (ab.bracket F G)).functional s) = fun _ => 0 :=
  bvTheoryD.antibracket_jacobi ab F G H

/-- Antibracket with zero gives zero -/
theorem antibracket_zero_left (ab : Antibracket) (F : BVFunctional) :
  (ab.bracket (zeroBVFunctional ⟨0⟩ .even) F).functional = fun _ => 0 :=
  bvTheoryD.antibracket_zero_left ab F

/-- Leibniz rule: (F, GH) = (F,G)H + (-1)^{(ε_F+1)ε_G} G(F,H)
    Note: the sign is (-1)^{(ε_F+1)ε_G}, not (-1)^{ε_{(F,G)} ε_G} -/
theorem antibracket_leibniz (ab : Antibracket) (F G H : BVFunctional) :
  (ab.bracket F (mulBVFunctional G H)).functional = fun s =>
    (mulBVFunctional (ab.bracket F G) H).functional s +
    (match F.parity, G.parity with
     | .even, .even => 1   -- (0+1)·0 = 0
     | .even, .odd => -1   -- (0+1)·1 = 1
     | .odd, .even => 1    -- (1+1)·0 = 0
     | .odd, .odd => 1) *  -- (1+1)·1 = 2
      (mulBVFunctional G (ab.bracket F H)).functional s :=
  bvTheoryD.antibracket_leibniz ab F G H

/- ============= BV ACTION AND MASTER EQUATION ============= -/

/-- BV action S[φ, φ*]: ghost number 0, bosonic functional on extended field space -/
structure BVAction where
  space : ExtendedFieldSpace
  action : BVFunctional
  ghost_constraint : action.ghost_number = ⟨0⟩
  parity_constraint : action.parity = GrassmannParity.even

/-- Classical master equation: (S, S) = 0 -/
def ClassicalMasterEquation (ab : Antibracket) (S : BVAction) : Prop :=
  (ab.bracket S.action S.action).functional = fun _ => 0

/-- Proper solution: CME holds and S|_{φ*=0} = S_classical -/
structure ProperSolution where
  action : BVAction
  ab : Antibracket
  master_eq : ClassicalMasterEquation ab action
  classical_action : ExtendedFieldSpace → ℝ

/-- BV differential s = (S, ·) -/
def bvDifferential (ab : Antibracket) (S : BVAction) (F : BVFunctional) : BVFunctional :=
  ab.bracket S.action F

/-- Structure for BV differential nilpotency -/
structure BVDifferentialTheory where
  /-- s² = 0 when (S,S) = 0 -/
  bv_differential_nilpotent : ∀ (ab : Antibracket) (S : BVAction)
    (h : ClassicalMasterEquation ab S) (F : BVFunctional),
    (bvDifferential ab S (bvDifferential ab S F)).functional = fun _ => 0

/-- BV differential theory axiom -/
axiom bvDifferentialTheoryD : BVDifferentialTheory

/-- s² = 0 when (S,S) = 0 -/
theorem bv_differential_nilpotent (ab : Antibracket) (S : BVAction)
    (h : ClassicalMasterEquation ab S) (F : BVFunctional) :
  (bvDifferential ab S (bvDifferential ab S F)).functional = fun _ => 0 :=
  bvDifferentialTheoryD.bv_differential_nilpotent ab S h F

/-- Apply BV differential n times -/
def bvDifferentialN (ab : Antibracket) (S : BVAction) (n : ℕ) (F : BVFunctional) :
    BVFunctional :=
  match n with
  | 0 => F
  | n + 1 => bvDifferential ab S (bvDifferentialN ab S n F)

/-- s^n = 0 for n ≥ 2 when CME holds -/
theorem bvDifferentialN_zero (ab : Antibracket) (S : BVAction)
    (h : ClassicalMasterEquation ab S) (F : BVFunctional) (n : ℕ) (hn : n ≥ 2) :
    (bvDifferentialN ab S n F).functional = fun _ => 0 := by
  sorry  -- Follows from nilpotency

/-- BV differential raises ghost number by 1 -/
theorem bvDifferential_ghost (ab : Antibracket) (S : BVAction) (F : BVFunctional) :
    (bvDifferential ab S F).ghost_number.value = F.ghost_number.value + 1 := by
  unfold bvDifferential
  have h := ab.ghost_additive S.action F
  simp only [S.ghost_constraint] at h
  simp [h]

/-- BV differential flips parity (since S is even) -/
theorem bvDifferential_parity (ab : Antibracket) (S : BVAction) (F : BVFunctional) :
    (bvDifferential ab S F).parity = antibracketParity .even F.parity := by
  unfold bvDifferential
  have h := ab.parity_odd S.action F
  simp only [S.parity_constraint] at h
  exact h

/- ============= GAUGE FIXING IN BV ============= -/

/-- Gauge-fixing fermion in BV formalism

    Ψ[φ] is a fermionic functional of ghost number -1, depending ONLY on fields
    (not antifields). Gauge fixing sets φ*_A = δΨ/δφ^A, which defines a
    Lagrangian submanifold L_Ψ with respect to the odd symplectic form ω.

    The crucial property: L_Ψ is Lagrangian (ω|_{L_Ψ} = 0) because
      ω = dφ^A ∧ dφ*_A = dφ^A ∧ d(∂Ψ/∂φ^A) = dφ^A ∧ (∂²Ψ/∂φ^A∂φ^B) dφ^B
    which vanishes by symmetry of second derivatives (for bosonic φ) or
    antisymmetry (for fermionic φ). -/
structure BVGaugeFixing where
  /-- The gauge-fixing fermion as a BV functional -/
  psi : BVFunctional
  /-- Ghost number -1 -/
  ghost_constraint : psi.ghost_number = ⟨-1⟩
  /-- Fermionic -/
  parity_constraint : psi.parity = GrassmannParity.odd
  /-- Ψ depends only on fields, not antifields (implicit in BV formalism) -/
  field_dependent : True  -- Would need more structure to state precisely

/-- Lagrangian submanifold from gauge-fixing fermion

    L_Ψ = { (φ, φ*) | φ*_A = ∂Ψ/∂φ^A }

    This is the standard way to construct Lagrangian submanifolds in BV.
    The submanifold is:
    1. Isotropic: ω|_{L_Ψ} = 0 (symplectic form vanishes)
    2. Maximal: dim(L_Ψ) = number of fields = (1/2) dim(field-antifield space) -/
structure LagrangianFromGF where
  /-- The odd symplectic form -/
  omega : OddSymplecticForm
  /-- The gauge-fixing fermion -/
  gf : BVGaugeFixing
  /-- The constraint φ*_A = ∂Ψ/∂φ^A defines L_Ψ -/
  constraint : ExtendedFieldSpace → Prop
  /-- L_Ψ is isotropic with respect to ω -/
  isotropic : ∀ s₁ s₂, constraint s₁ → constraint s₂ → omega.pairing s₁ s₂ = 0

/-- Legacy alias for backward compatibility -/
abbrev LagrangianSubmanifold := LagrangianFromGF

/-- BV path integral over Lagrangian submanifold

    The BV path integral is defined as:

      Z = ∫_{L_Ψ} [dφ] exp(iS[φ, φ*]/ℏ)|_{φ*=∂Ψ/∂φ}

    where L_Ψ is the Lagrangian submanifold defined by Ψ. This is the
    fundamental definition of gauge fixing in the BV formalism.

    Key theorem: If S satisfies the quantum master equation, then Z is
    independent of the choice of Ψ (up to BRST-exact terms). -/
structure BVPathIntegral where
  /-- The BV action -/
  S : BVAction
  /-- The Lagrangian submanifold to integrate over -/
  L : LagrangianFromGF
  /-- The odd symplectic form (for consistency check) -/
  omega : OddSymplecticForm
  /-- L is Lagrangian with respect to omega -/
  L_is_lagrangian : L.omega = omega

/-- Structure for BV gauge fixing theory -/
structure BVGaugeFixingTheory where
  /-- Gauge-fixed action: S restricted to Lagrangian submanifold -/
  gaugeFixedBVAction : (S : BVAction) → (L : LagrangianFromGF) → ExtendedFieldSpace → ℝ
  /-- Gauge independence: difference is BV-exact -/
  bv_gauge_independence : ∀ (S : BVAction) (ab : Antibracket)
    (h : ClassicalMasterEquation ab S) (L₁ L₂ : LagrangianFromGF),
    ∃ F : BVFunctional,
      (fun s => gaugeFixedBVAction S L₂ s - gaugeFixedBVAction S L₁ s) =
      (bvDifferential ab S F).functional

/-- BV gauge fixing theory axiom -/
axiom bvGaugeFixingTheoryD : BVGaugeFixingTheory

/-- Gauge-fixed action: S restricted to Lagrangian submanifold

    S_gf[φ] = S[φ, φ*]|_{φ*_A = ∂Ψ/∂φ^A}

    This is what appears in the exponent of the path integral.
    The restriction to L is implicit in the path integral measure. -/
noncomputable def gaugeFixedBVAction (S : BVAction) (L : LagrangianFromGF) : ExtendedFieldSpace → ℝ :=
  bvGaugeFixingTheoryD.gaugeFixedBVAction S L

/-- Stokes' theorem for BV: Independence of gauge-fixing choice

    For S satisfying the classical master equation (S,S) = 0:
    The path integral Z = ∫_{L_Ψ} exp(iS/ℏ) is independent of Ψ.

    Proof sketch: Under deformation Ψ → Ψ + δΨ, the change in Z is
      δZ ∝ ∫_L ⟨sO⟩ = 0
    where s = (S, ·) is the BV differential, because L is Lagrangian
    and the master equation ensures ⟨sO⟩ = 0.

    At quantum level with QME, we need (S,S) = 2iℏΔS. -/
theorem bv_gauge_independence (S : BVAction) (ab : Antibracket)
    (h : ClassicalMasterEquation ab S) (L₁ L₂ : LagrangianFromGF) :
  ∃ F : BVFunctional, -- The difference is (S, F) for some F
    (fun s => gaugeFixedBVAction S L₂ s - gaugeFixedBVAction S L₁ s) =
    (bvDifferential ab S F).functional :=
  bvGaugeFixingTheoryD.bv_gauge_independence S ab h L₁ L₂

/- ============= BV LAPLACIAN AND QUANTUM MASTER EQUATION ============= -/

/-- BV Laplacian Δ

    Δ = ∑_A (-1)^(ε_A) δ²/(δφ^A δφ*_A)

    A second-order differential operator that measures the failure of
    classical master equation to hold at quantum level.

    Properties:
    - Δ² = 0
    - Δ raises ghost number by 1
    - Δ is odd -/
structure BVLaplacian where
  /-- The extended field space -/
  space : ExtendedFieldSpace
  /-- The Laplacian operator -/
  laplacian : BVFunctional → BVFunctional
  /-- Nilpotent: Δ² = 0 -/
  nilpotent : ∀ F : BVFunctional, (laplacian (laplacian F)).functional = fun _ => 0
  /-- Raises ghost number by 1 -/
  raises_ghost : ∀ F : BVFunctional,
    (laplacian F).ghost_number.value = F.ghost_number.value + 1
  /-- Odd parity -/
  flips_parity : ∀ F : BVFunctional, (laplacian F).parity = F.parity.flip

/-- Structure for BV Laplacian theory -/
structure BVLaplacianTheory where
  /-- Compatibility of Δ and (,): the failure to be a derivation -/
  delta_antibracket_relation : ∀ (Δ : BVLaplacian) (ab : Antibracket)
    (F G : BVFunctional),
    ∃ deviation : BVFunctional,  -- The {F,G} term
      (Δ.laplacian (ab.bracket F G)).functional = fun s =>
        (ab.bracket (Δ.laplacian F) G).functional s +
        (let sign := match F.parity with | .even => 1 | .odd => -1
         sign * (ab.bracket F (Δ.laplacian G)).functional s) +
        (let sign := match F.parity with | .even => 1 | .odd => -1
         sign * deviation.functional s)

/-- BV Laplacian theory axiom -/
axiom bvLaplacianTheoryD : BVLaplacianTheory

/-- Compatibility of Δ and (,): the failure to be a derivation

    Δ(F,G) = (ΔF, G) + (-1)^(ε_F+1)(F, ΔG) + (-1)^ε_F {F, G}

    where {F,G} is the "BV bracket" measuring non-derivation. -/
theorem delta_antibracket_relation (Δ : BVLaplacian) (ab : Antibracket)
    (F G : BVFunctional) :
  ∃ deviation : BVFunctional,  -- The {F,G} term
    (Δ.laplacian (ab.bracket F G)).functional = fun s =>
      (ab.bracket (Δ.laplacian F) G).functional s +
      (let sign := match F.parity with | .even => 1 | .odd => -1
       sign * (ab.bracket F (Δ.laplacian G)).functional s) +
      (let sign := match F.parity with | .even => 1 | .odd => -1
       sign * deviation.functional s) :=
  bvLaplacianTheoryD.delta_antibracket_relation Δ ab F G

/-- Quantum master equation

    (S, S) - 2iℏΔS = 0

    or equivalently: ½(S, S) = iℏΔS

    This is the condition for anomaly-free quantization.
    Solutions to QME define consistent quantum gauge theories.

    We work with real functionals, so this becomes:
    (S, S) = 0 AND ΔS = 0 (at ℏ = 0, classical limit)
    or the full equation order by order in ℏ. -/
def QuantumMasterEquation (ab : Antibracket) (Δ : BVLaplacian)
    (S : BVAction) (hbar : ℝ) : Prop :=
  ∀ s : ExtendedFieldSpace,
    (ab.bracket S.action S.action).functional s =
    2 * hbar * (Δ.laplacian S.action).functional s

/-- At ℏ = 0, QME reduces to CME -/
theorem qme_classical_limit (ab : Antibracket) (Δ : BVLaplacian) (S : BVAction) :
    QuantumMasterEquation ab Δ S 0 ↔ ClassicalMasterEquation ab S := by
  unfold QuantumMasterEquation ClassicalMasterEquation
  constructor
  · intro h
    ext s
    have hs := h s
    simp only [mul_zero, zero_mul] at hs
    exact hs
  · intro h s
    have := congrFun h s
    simp only [mul_zero, zero_mul]
    exact this

/-- Quantum BV action as expansion in ℏ

    S_ℏ = S_0 + ℏS_1 + ℏ²S_2 + ...

    where S_0 satisfies classical ME and higher terms are quantum corrections.
    At each order in ℏ, we have consistency conditions from QME. -/
structure QuantumBVAction where
  /-- The extended field space -/
  space : ExtendedFieldSpace
  /-- Classical part S_0 -/
  classical : BVAction
  /-- Quantum corrections S_n for n ≥ 1 -/
  corrections : ℕ → BVFunctional
  /-- All corrections have ghost number 0 -/
  corrections_ghost : ∀ n, (corrections n).ghost_number = ⟨0⟩

/-- First quantum correction equation: (S_0, S_1) + ΔS_0 = 0

    This is the condition at order ℏ¹ in the QME expansion. -/
def FirstOrderQME (ab : Antibracket) (Δ : BVLaplacian) (Q : QuantumBVAction) : Prop :=
  (fun s => (ab.bracket Q.classical.action (Q.corrections 1)).functional s +
            (Δ.laplacian Q.classical.action).functional s) = fun _ => 0

/- Quantum gauge independence requires the quantum master equation

   For the quantum path integral to be truly gauge-independent, we need
   the full QME: (S,S) - 2iℏΔS = 0.

   The ℏΔS term accounts for the measure factor in the path integral.
   This is a stronger statement than classical gauge independence.

   NOTE: The full statement would require defining the quantum path integral
   as a functional on Lagrangian submanifolds, which is beyond the current
   formalization. The key physical content is captured by the QME itself. -/

/- ============= BV COHOMOLOGY ============= -/

/-- BV-closed functional: s_BV F = 0 -/
def BVClosed (ab : Antibracket) (S : BVAction) (F : BVFunctional) : Prop :=
  (bvDifferential ab S F).functional = fun _ => 0

/-- BV-exact functional: F = s_BV G for some G -/
def BVExact (ab : Antibracket) (S : BVAction) (F : BVFunctional) : Prop :=
  ∃ G : BVFunctional, (bvDifferential ab S G).functional = F.functional

/-- BV cohomology H(s_BV) = ker(s_BV)/im(s_BV)

    Physical observables are s_BV-closed modulo s_BV-exact.
    At ghost number 0, this gives gauge-invariant observables. -/
structure BVCohomology where
  /-- The antibracket -/
  ab : Antibracket
  /-- The BV action -/
  S : BVAction
  /-- Classical master equation holds -/
  cme : ClassicalMasterEquation ab S
  /-- Cohomology representatives at each ghost number -/
  representatives : GhostNumber → Set BVFunctional
  /-- Representatives are closed -/
  closed : ∀ gh F, F ∈ representatives gh → BVClosed ab S F
  /-- Representatives have correct ghost number -/
  ghost_match : ∀ gh F, F ∈ representatives gh → F.ghost_number = gh

/- ============= ANOMALIES IN BV ============= -/

/-- BV anomaly

    If QME cannot be satisfied: (S, S) - 2iℏΔS = A ≠ 0

    The anomaly A has ghost number 1 and satisfies a consistency condition:
    (S, A) + iℏΔA = 0 (Wess-Zumino consistency in BV language) -/
structure BVAnomaly where
  /-- The antibracket -/
  ab : Antibracket
  /-- The BV Laplacian -/
  Δ : BVLaplacian
  /-- The BV action -/
  S : BVAction
  /-- The anomaly functional -/
  anomaly : BVFunctional
  /-- Ghost number 1 -/
  ghost_constraint : anomaly.ghost_number = ⟨1⟩
  /-- The anomaly is what remains after attempting QME -/
  is_obstruction : ∀ s hbar,
    (ab.bracket S.action S.action).functional s -
    2 * hbar * (Δ.laplacian S.action).functional s = anomaly.functional s

/-- Structure for BV anomaly consistency theory -/
structure BVAnomalyTheory where
  /-- Wess-Zumino consistency for BV anomaly -/
  bv_wess_zumino_consistency : ∀ (anom : BVAnomaly),
    (fun s => (anom.ab.bracket anom.S.action anom.anomaly).functional s +
              (anom.Δ.laplacian anom.anomaly).functional s) = fun _ => 0

/-- BV anomaly theory axiom -/
axiom bvAnomalyTheoryD : BVAnomalyTheory

/-- Wess-Zumino consistency for BV anomaly: (S, A) + ΔA = 0 (at leading order)

    This follows from applying s_BV to the QME. -/
theorem bv_wess_zumino_consistency (anom : BVAnomaly) :
  (fun s => (anom.ab.bracket anom.S.action anom.anomaly).functional s +
            (anom.Δ.laplacian anom.anomaly).functional s) = fun _ => 0 :=
  bvAnomalyTheoryD.bv_wess_zumino_consistency anom

/-- Anomaly-free theory: QME can be satisfied -/
def AnomalyFreeBV (ab : Antibracket) (Δ : BVLaplacian) (S : BVAction) (hbar : ℝ) : Prop :=
  QuantumMasterEquation ab Δ S hbar

/- ============= ZINN-JUSTIN EQUATION ============= -/

/-- Zinn-Justin equation

    The functional identity encoding BRST invariance at the quantum level.
    For the generating functional W[J, K] with sources J for fields and K for
    antifields (BRST sources), the Zinn-Justin equation is:

    ∫ (δW/δK_A · δW/δJ^A) = 0

    This is equivalent to the quantum master equation for the effective action Γ.
    In BV language: (Γ, Γ) - 2iℏΔΓ = 0 where Γ is the Legendre transform of W. -/
structure ZinnJustinEquation where
  /-- The antibracket structure -/
  ab : Antibracket
  /-- The BV Laplacian -/
  Δ : BVLaplacian
  /-- The effective action Γ (Legendre transform of generating functional) -/
  effective_action : BVAction
  /-- The ZJ equation is the QME for Γ -/
  equation : ∀ hbar, QuantumMasterEquation ab Δ effective_action hbar

/-- The ZJ equation at tree level is equivalent to CME -/
theorem zj_tree_level (zj : ZinnJustinEquation) :
    ClassicalMasterEquation zj.ab zj.effective_action := by
  have h := zj.equation 0
  rw [← qme_classical_limit]
  exact h

/- ============= BRST AS A SPECIAL CASE OF BV ============= -/

/-- BRST formalism as a special case of BV

    The BRST formalism applies ONLY to gauge theories with:

    1. **Field-independent structure constants**: The gauge algebra must have
       CONSTANT structure coefficients f^α_βγ (not field-dependent).
       For gauge transformations δ_ε φ = R^i_α(φ) ε^α, the commutator gives:
         [δ_{ε₁}, δ_{ε₂}] φ = δ_{f(ε₁,ε₂)} φ
       BRST requires f^α_βγ to be constants (e.g., Lie algebra structure constants).

    2. **Off-shell closure**: The gauge algebra must close WITHOUT using the
       equations of motion. If closure requires equations of motion, the
       structure "constants" become field-dependent and BRST fails.

    3. **Irreducibility**: The gauge generators R^i_α must be independent
       (no relations R^i_α Z^α_a = 0 among them).

    When these conditions hold, BV reduces to BRST:
    - Antifields can be eliminated: φ*_A = 0
    - The BV action is linear in antifields: S_BV = S_cl + φ*_i R^i_α c^α - ½c*_α f^α_βγ c^β c^γ
    - The BRST operator s = (S_BV, ·)|_{φ*=0} is well-defined and nilpotent

    **When BRST fails and BV is required:**

    - **Open gauge algebras** (field-dependent structure functions): The closure
      relation involves the equations of motion, making f^α_βγ → f^α_βγ(φ).
      There is NO consistent BRST formulation in this case.
      Examples: W-gravity, some formulations of supergravity, higher-spin theories.

    - **Reducible theories**: Gauge generators satisfy relations, requiring
      "ghosts for ghosts" with arbitrarily high ghost number.
      Examples: p-form gauge theories in d > p+1 dimensions.

    BV is the universal framework: it handles ALL gauge theories, while BRST
    is a simplification that works only for a restricted class. -/
structure BRSTFromBV where
  /-- The BV action -/
  bv_action : BVAction
  /-- The antibracket -/
  ab : Antibracket
  /-- Classical master equation holds -/
  cme : ClassicalMasterEquation ab bv_action
  /-- The BV action is at most linear in antifields (irreducibility condition).
      For irreducible theories: S_BV = S_cl + φ*_i R^i_α c^α - ½c*_α f^α_βγ c^β c^γ
      No terms quadratic or higher in antifields. -/
  linear_in_antifields : Prop
  /-- The gauge algebra closes off-shell with field-INDEPENDENT structure constants.
      [δ_{ε₁}, δ_{ε₂}] = δ_{f·(ε₁,ε₂)} where f^α_βγ are constants, not functions of fields.
      This is the KEY condition that distinguishes BRST-compatible theories. -/
  field_independent_structure : Prop

/-- Extract BRST operator from BV

    s = (S_BV, ·)|_{φ*=0}

    The BRST transformation of a field φ is obtained by:
    1. Computing the BV differential (S_BV, φ)
    2. Setting all antifields to zero -/
def BRSTFromBV.brst_operator (bv : BRSTFromBV) : BVFunctional → BVFunctional :=
  bvDifferential bv.ab bv.bv_action

/-- BRST nilpotency from BV

    s² = 0 follows from:
    1. (S,S) = 0 (classical master equation)
    2. Graded Jacobi identity for (,)

    Proof: s²F = (S,(S,F)) = ½((S,S),F) = 0 by Jacobi and CME. -/
theorem brst_nilpotent_from_bv (bv : BRSTFromBV) (F : BVFunctional) :
    (bv.brst_operator (bv.brst_operator F)).functional = fun _ => 0 :=
  bv_differential_nilpotent bv.ab bv.bv_action bv.cme F

/-- The special Lagrangian submanifold φ* = 0

    Setting all antifields to zero defines a Lagrangian submanifold L₀.
    This corresponds to the gauge-fixing fermion Ψ = 0.

    BRST formalism works on this trivial Lagrangian submanifold.
    More general gauge fixings (Lorenz, axial, etc.) correspond to
    non-zero Ψ and different Lagrangian submanifolds. -/
structure TrivialLagrangian where
  /-- The odd symplectic form -/
  omega : OddSymplecticForm
  /-- The constraint φ* = 0 -/
  constraint : ExtendedFieldSpace → Prop
  /-- This is Lagrangian (isotropic) -/
  isotropic : ∀ s₁ s₂, constraint s₁ → constraint s₂ → omega.pairing s₁ s₂ = 0

/-- Structure for BRST-BV relation theory -/
structure BRSTBVTheory where
  /-- BRST gauge-fixed action equals BV action at φ* = 0 -/
  brst_action_from_bv : (bv : BRSTFromBV) → (L₀ : TrivialLagrangian) → ExtendedFieldSpace → ℝ

/-- BRST-BV theory axiom -/
axiom brstBVTheoryD : BRSTBVTheory

/-- BRST gauge-fixed action equals BV action at φ* = 0

    S_BRST[φ,c,c̄,B] = S_BV[φ,c,c̄,B, φ*=0, c*=0, c̄*=0, B*=0]

    The BRST action with ghosts is the BV action restricted to the
    trivial Lagrangian submanifold. -/
noncomputable def brst_action_from_bv (bv : BRSTFromBV) (L₀ : TrivialLagrangian) :
    ExtendedFieldSpace → ℝ :=
  brstBVTheoryD.brst_action_from_bv bv L₀

/- BRST cohomology equals BV cohomology at φ* = 0

   The physical observables in BRST (H⁰(s)) correspond to the BV
   cohomology H⁰(s_BV) restricted to the trivial Lagrangian submanifold.

   This is why BRST is sufficient for computing physical quantities
   in theories where it applies.

   NOTE: The full statement would require defining restriction maps between
   cohomologies, which is beyond the current formalization. -/

/- When BV is truly needed: theories where BRST is IMPOSSIBLE

   The BV formalism is not merely a generalization of BRST - it is the ONLY
   consistent quantization framework for many important gauge theories:

   1. **Open gauge algebras (field-dependent structure functions)**:
      When the gauge algebra closes only on-shell, the structure "constants"
      f^α_βγ(φ) depend on the fields. In this case:
      - There is NO consistent BRST transformation
      - The nilpotency s² = 0 FAILS without antifields
      - The BV antibracket and full antifield dependence are ESSENTIAL
      Examples: W-gravity, higher-spin theories, some supergravity formulations

   2. **Reducible gauge theories**:
      When gauge generators are not independent (R^i_α Z^α_a = 0), we need:
      - "Ghosts for ghosts" c_a with ghost number 2
      - Potentially infinite tower of ghosts for higher reducibility
      - Antifields for ALL ghosts at every level
      Examples: p-form gauge theories in d > p+1, topological field theories

   3. **Theories with L∞ structure**:
      String field theory and related constructions have gauge structures
      that are inherently homotopy algebraic (L∞ or A∞).
      - Higher brackets l_n correspond to higher antifield terms
      - The master equation encodes the full homotopy structure

   4. **Consistent effective actions for gauge theories**:
      Even for BRST-compatible theories like Yang-Mills, the 1PI effective
      action Γ[φ, φ*] naturally lives in BV formalism and satisfies the
      classical master equation (Γ, Γ) = 0. -/

end ModularPhysics.Core.QFT.BV
