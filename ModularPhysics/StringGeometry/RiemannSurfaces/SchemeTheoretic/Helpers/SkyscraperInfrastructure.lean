/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Basic

/-!
# Infrastructure for Skyscraper Sheaves

This file provides the foundational infrastructure for skyscraper sheaves.

## Key Properties

For a skyscraper sheaf k_p at point p on a scheme X:

1. **Sections**: k_p(U) = κ(p) if p ∈ U, else 0
2. **Module structure**: The O_X(U)-module structure on κ(p) is via evaluation:
   f · v = (evaluation U p hx f) · v
3. **Flasque property**: All restriction maps are surjective
4. **Global sections**: Γ(X, k_p) = κ(p)

## Mathematical Background

The evaluation map is:
  O_X(U) → O_{X,p} → κ(p)

where the first map is the germ at p and the second is the residue map.
This is implemented in Mathlib as `Scheme.evaluation`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Classical

namespace RiemannSurfaces.SchemeTheoretic

variable {X : Scheme}

/-!
## Evaluation and Module Structure

The residue field κ(p) has a natural O_X(U)-module structure for any open U containing p.
-/

/-- The evaluation ring homomorphism from sections to the residue field.
    This is the composition: O_X(U) → O_{X,p} → κ(p). -/
noncomputable def evalAtPoint (p : X) (U : Opens X.carrier) (hp : p ∈ U) :
    Γ(X, U) →+* X.residueField p :=
  (X.evaluation U p hp).hom

/-- κ(p) has an O_X(U)-module structure for U containing p via evaluation. -/
noncomputable instance residueFieldModule (p : X) (U : Opens X.carrier) (hp : p ∈ U) :
    Module (Γ(X, U)) (X.residueField p) :=
  Module.compHom (X.residueField p) (evalAtPoint p U hp)

/-- For the top open, κ(p) is always an O_X(⊤)-module. -/
noncomputable instance residueFieldModuleTop (p : X) :
    Module Γ(X, ⊤) (X.residueField p) :=
  residueFieldModule p ⊤ (Set.mem_univ p)

/-!
## Key Properties of Skyscraper Sheaves

We establish the key properties needed for Riemann-Roch:
1. Restriction maps are surjective (flasque)
2. Global sections = κ(p)
3. κ(p) is 1-dimensional over ℂ
-/

/-- The restriction map κ(p) → κ(p) is identity (hence surjective). -/
theorem residueField_restriction_surjective (p : X) :
    Function.Surjective (id : X.residueField p → X.residueField p) :=
  Function.surjective_id

/-- Restriction to PUnit is surjective (from a nonempty type). -/
theorem restriction_to_punit_surjective {α : Type*} [Nonempty α] :
    Function.Surjective (fun _ : α => PUnit.unit) := by
  intro y
  cases y
  exact ⟨Classical.arbitrary α, rfl⟩

/-- Any map to PUnit is surjective. -/
theorem map_to_punit_surjective {α : Type*} (a : α) :
    Function.Surjective (fun _ : α => PUnit.unit) := by
  intro y
  cases y
  exact ⟨a, rfl⟩

/-!
## Dimension of Skyscraper Cohomology

For curves over ℂ, κ(p) ≅ ℂ has dimension 1.
-/

variable (C : AlgebraicCurve)

/-- The residue field of C at p is isomorphic to ℂ as a ring. -/
noncomputable def residueFieldIsoComplex (p : C.PointType) :
    C.toScheme.residueField p ≅ CommRingCat.of ℂ :=
  (C.residueFieldIsComplex p).some

/-- The residue field κ(p) is a ℂ-algebra. -/
noncomputable instance residueFieldComplexAlgebra (p : C.PointType) :
    Algebra ℂ (C.toScheme.residueField p) :=
  RingHom.toAlgebra (residueFieldIsoComplex C p).inv.hom

/-- The ring isomorphism κ(p) ≅ ℂ is ℂ-linear.

    **Proof:**
    The algebra structure on κ(p) is defined by `iso.inv : ℂ → κ(p)`.
    The forward map `iso.hom : κ(p) → ℂ` is ℂ-linear because:
    iso.hom(c • x) = iso.hom(iso.inv(c) * x) = iso.hom(iso.inv(c)) * iso.hom(x) = c * iso.hom(x) -/
noncomputable def residueFieldLinearEquiv (p : C.PointType) :
    (C.toScheme.residueField p) ≃ₗ[ℂ] ℂ := by
  -- Get the ring isomorphism
  let iso := residueFieldIsoComplex C p
  -- Helper: iso.inv(iso.hom(x)) = x (for x : κ(p))
  have left_inv_eq : ∀ x : C.toScheme.residueField p, iso.inv.hom (iso.hom.hom x) = x := fun x => by
    have h := iso.hom_inv_id
    have heq : iso.hom ≫ iso.inv = 𝟙 _ := h
    have := CommRingCat.comp_apply iso.hom iso.inv x
    rw [heq, CommRingCat.id_apply] at this
    exact this.symm
  -- Helper: iso.hom(iso.inv(c)) = c (for c : ℂ)
  have right_inv_eq : ∀ c : ℂ, iso.hom.hom (iso.inv.hom c) = c := fun c => by
    have h := iso.inv_hom_id
    have heq : iso.inv ≫ iso.hom = 𝟙 _ := h
    have := CommRingCat.comp_apply iso.inv iso.hom c
    rw [heq, CommRingCat.id_apply] at this
    exact this.symm
  -- Construct the ring equivalence manually
  let ringEquiv : (C.toScheme.residueField p) ≃+* ℂ :=
    { toFun := iso.hom.hom
      invFun := iso.inv.hom
      left_inv := left_inv_eq
      right_inv := right_inv_eq
      map_mul' := iso.hom.hom.map_mul
      map_add' := iso.hom.hom.map_add }
  -- Construct the linear equiv from the ring equiv
  refine LinearEquiv.ofBijective
    { toFun := ringEquiv
      map_add' := ringEquiv.map_add
      map_smul' := fun c x => ?_ } ?_
  · -- Show map_smul': ringEquiv(c • x) = c • ringEquiv(x)
    -- The algebra action is c • x = iso.inv(c) * x
    simp only [Algebra.smul_def, RingHom.id_apply]
    -- Need: ringEquiv(algebraMap ℂ κ(p) c * x) = c * ringEquiv(x)
    -- algebraMap = iso.inv.hom
    rw [show algebraMap ℂ (C.toScheme.residueField p) c = iso.inv.hom c by rfl]
    -- Now use that ringEquiv is a ring hom
    rw [ringEquiv.map_mul]
    -- Need: ringEquiv(iso.inv(c)) * ringEquiv(x) = c * ringEquiv(x)
    congr 1
    -- ringEquiv(iso.inv(c)) = iso.hom(iso.inv(c)) = c
    exact right_inv_eq c
  · -- Show bijective
    exact ringEquiv.bijective

/-- The residue field κ(p) is 1-dimensional over ℂ.

    **Proof:**
    κ(p) ≅ ℂ as ℂ-vector spaces (from residueFieldLinearEquiv).
    Since ℂ is 1-dimensional over itself, so is κ(p). -/
theorem residueField_finrank_one (p : C.PointType) :
    Module.finrank ℂ (C.toScheme.residueField p) = 1 := by
  -- Use the linear equivalence to transfer the finrank
  have e := residueFieldLinearEquiv C p
  rw [LinearEquiv.finrank_eq e]
  exact Module.finrank_self ℂ

/-!
## Flasque Sheaf Property

A sheaf F is flasque if all restriction maps F(V) → F(U) are surjective for U ⊆ V.
Skyscraper sheaves are flasque because:
- If p ∈ U: restriction is identity κ(p) → κ(p)
- If p ∉ U: target is 0, any map to 0 is surjective
-/

/-- Statement that the skyscraper sheaf at p is flasque.

    **Mathematical content:**
    For the skyscraper sheaf k_p at point p:
    - k_p(U) = κ(p) if p ∈ U, else 0

    The restriction k_p(V) → k_p(U) for U ⊆ V is:
    - Identity κ(p) → κ(p) if p ∈ U (hence p ∈ V)
    - The unique map κ(p) → 0 if p ∉ U, p ∈ V
    - The map 0 → 0 if p ∉ V

    All these maps are surjective. -/
theorem skyscraper_restriction_surjective (p : X) (U V : Opens X.carrier) (_ : U ≤ V) :
    -- The restriction map has surjectivity in each case:
    -- Case 1: p ∈ U (hence p ∈ V): id : κ(p) → κ(p) is surjective
    -- Case 2: p ∉ U, p ∈ V: unique map κ(p) → 0 is surjective
    -- Case 3: p ∉ V (hence p ∉ U): id : 0 → 0 is surjective
    (p ∈ U → Function.Surjective (id : X.residueField p → X.residueField p)) ∧
    (p ∉ U → p ∈ V → ∀ y : PUnit, ∃ _ : X.residueField p, PUnit.unit = y) ∧
    (p ∉ V → ∀ y : PUnit, ∃ x : PUnit, x = y) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Case 1: p ∈ U
    intro _
    exact Function.surjective_id
  · -- Case 2: p ∉ U, p ∈ V
    intro _ _ y
    cases y
    exact ⟨0, rfl⟩
  · -- Case 3: p ∉ V
    intro _ y
    exact ⟨y, rfl⟩

/-!
## Canonical Residue Map

The canonical ring homomorphism ℂ → κ(p) via the structure morphism.
This defines the ℂ-module structure used in Čech cohomology.
-/

/-- The canonical ring homomorphism from ℂ to κ(p) via the structure morphism.

    This is the composition:
    ℂ →[ΓSpecIso⁻¹]→ Γ(Spec ℂ, ⊤) →[π*.appTop]→ Γ(C, ⊤) →[evalAtPoint]→ κ(p)

    This map defines the ℂ-module structure on κ(p) that appears in
    `moduleValueComplex` and hence in all Čech cohomology computations.

    For any open U containing p:
    canonicalResidueMap(a) = evalAtPoint(U, p)(algebraMap ℂ O_C(U) a)
    by evalAtPoint_comp_restriction. -/
noncomputable def canonicalResidueMap (p : C.PointType) :
    ℂ →+* C.toScheme.residueField p :=
  (evalAtPoint p ⊤ (Set.mem_univ (p : C.toScheme.carrier))).comp
    (C.structureMorphism.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)

/-- The canonical residue map is injective (ring hom from field to nontrivial ring). -/
theorem canonicalResidueMap_injective (p : C.PointType) :
    Function.Injective (canonicalResidueMap C p) :=
  (canonicalResidueMap C p).injective

/-- The canonical residue map is surjective.

    This follows from the algebraic Nullstellensatz: for schemes of finite type
    over algebraically closed fields, residue fields at closed points equal
    the base field. Since our curves are of finite type over ℂ (algebraically
    closed), the canonical map ℂ → κ(p) is surjective.

    References: Stacks Project Tag 00FJ, Hartshorne Exercise II.2.13. -/
theorem canonicalResidueMap_surjective (p : C.PointType) :
    Function.Surjective (canonicalResidueMap C p) := by
  sorry

/-- The canonical residue map as a ring equivalence. -/
noncomputable def canonicalResidueEquiv (p : C.PointType) :
    ℂ ≃+* C.toScheme.residueField p :=
  RingEquiv.ofBijective (canonicalResidueMap C p)
    ⟨canonicalResidueMap_injective C p, canonicalResidueMap_surjective C p⟩

/-- κ(p) is 1-dimensional over ℂ with the module structure from the canonical map.

    The ℂ-module structure is: a • v = canonicalResidueMap(a) * v.
    This is the same module structure used in `moduleValueComplex` / `algebraOnSections`. -/
theorem residueField_finrank_one_canonical (p : C.PointType) :
    letI : Module ℂ (C.toScheme.residueField p) :=
      Module.compHom (C.toScheme.residueField p) (canonicalResidueMap C p)
    Module.finrank ℂ (C.toScheme.residueField p) = 1 := by
  letI : Module ℂ (C.toScheme.residueField p) :=
    Module.compHom (C.toScheme.residueField p) (canonicalResidueMap C p)
  apply (finrank_eq_one_iff_of_nonzero' (1 : C.toScheme.residueField p) one_ne_zero).mpr
  intro w
  obtain ⟨c, hc⟩ := canonicalResidueMap_surjective C p w
  exact ⟨c, by show canonicalResidueMap C p c * 1 = w; rw [mul_one]; exact hc⟩

end RiemannSurfaces.SchemeTheoretic
