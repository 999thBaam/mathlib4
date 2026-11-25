/-
Copyright (c) 2026 Amit Bagra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amit Bagra
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Conjugation as an automorphism of a normal subgroup

Conjugation by `g : G` maps a normal subgroup `H` onto itself, so it restricts to an
automorphism of `H`. This file packages that restriction as `Subgroup.conjAut`, and the
resulting action of `G` on `MulAut H` as `Subgroup.conjAutHom`.

The main application is `Subgroup.normal_map_subtype_of_characteristic`: a characteristic
subgroup of a normal subgroup is normal in the ambient group. Characteristicity of `K ≤ H`
is a statement about `MulAut H`, so turning conjugation by an element of `G` into an
element of `MulAut H` is exactly what is needed to apply it.

## Main definitions

* `Subgroup.conjAut H g` — conjugation by `g : G` as an automorphism of a normal subgroup
  `H`, acting as `x ↦ g * x * g⁻¹`.
* `Subgroup.conjAutHom H` — the same data bundled as a homomorphism `G →* MulAut H`.

## Main results

* `Subgroup.normal_map_subtype_of_characteristic` — a characteristic subgroup of a normal
  subgroup is normal.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Conjugation by `g : G`, restricted to a normal subgroup `H`, as an automorphism of `H`.

Its action is `x ↦ g * x * g⁻¹`, see `Subgroup.coe_conjAut`. -/
def conjAut (H : Subgroup G) [H.Normal] (g : G) : MulAut H :=
  ((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr (Normal.map_conj_eq H g))

@[simp]
theorem coe_conjAut (H : Subgroup G) [H.Normal] (g : G) (x : H) :
    ((conjAut H g x : H) : G) = g * x * g⁻¹ := rfl

@[simp]
theorem coe_conjAut_symm (H : Subgroup G) [H.Normal] (g : G) (x : H) :
    (((conjAut H g).symm x : H) : G) = g⁻¹ * x * g := rfl

/-- Conjugation as a homomorphism from `G` to the automorphism group of a normal
subgroup `H`. -/
def conjAutHom (H : Subgroup G) [H.Normal] : G →* MulAut H where
  toFun := conjAut H
  map_one' := by ext x; simp
  map_mul' g₁ g₂ := by ext x; simp [mul_assoc]

@[simp]
theorem conjAutHom_apply (H : Subgroup G) [H.Normal] (g : G) : conjAutHom H g = conjAut H g :=
  rfl

/-- **A characteristic subgroup of a normal subgroup is normal.** If `H ⊴ G` and `K` is
characteristic in `H`, then `K`, viewed inside `G`, is normal in `G`. -/
theorem normal_map_subtype_of_characteristic {H : Subgroup G} [H.Normal] (K : Subgroup H)
    [K.Characteristic] : (K.map H.subtype).Normal :=
  ⟨fun n hn g => by
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hn
    refine mem_map.mpr ⟨conjAut H g y, ?_, ?_⟩
    · exact characteristic_iff_map_le.mp ‹K.Characteristic› (conjAut H g)
        (mem_map_of_mem _ hy)
    · simp⟩

end Subgroup
