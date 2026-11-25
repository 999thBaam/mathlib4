/-
Copyright (c) 2026 Amit Bagra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amit Bagra
-/
module

public import Mathlib.GroupTheory.Nilpotent

/-!
# The `p`-core and the Fitting subgroup

For a group `G` and a natural number `p`, the **`p`-core** `O_p(G)` is the largest normal
`p`-subgroup of `G`, defined here as the supremum of all normal `p`-subgroups. That this
supremum is itself a `p`-group is `Subgroup.isPGroup_pCore`, so `O_p(G)` really is the
largest one.

For a finite group the **Fitting subgroup** `F(G)` is the join of the `p`-cores over the
prime factors of `|G|`. It is nilpotent (`Subgroup.isNilpotent_fittingSubgroup`) and
contains every normal nilpotent subgroup (`Subgroup.le_fittingSubgroup`), so it is the
largest normal nilpotent subgroup of `G`.

## Main definitions

* `Subgroup.pCore p G` — the `p`-core `O_p(G)`.
* `Subgroup.fittingSubgroup G` — the Fitting subgroup `F(G)`.

## Main results

* `Subgroup.isPGroup_pCore` — `O_p(G)` is a `p`-group.
* `Subgroup.le_pCore` — `O_p(G)` contains every normal `p`-subgroup.
* `Subgroup.disjoint_pCore` — `O_p(G)` and `O_q(G)` are disjoint for `p ≠ q`.
* `Subgroup.commute_pCore` — elements of `O_p(G)` and `O_q(G)` commute for `p ≠ q`.
* `Subgroup.isNilpotent_fittingSubgroup` — **`F(G)` is nilpotent.**
* `Subgroup.le_fittingSubgroup` — **`F(G)` contains every normal nilpotent subgroup**, so
  it is the largest one.
* `Subgroup.isNilpotent_iff_fittingSubgroup_eq_top` — `G` is nilpotent iff `F(G) = ⊤`.

## Implementation notes

The textbook proof of Fitting's theorem — that a product of two normal nilpotent subgroups
is nilpotent — goes through class additivity and a good deal of commutator bookkeeping. The
route here avoids that, following `Sylow.directProductOfNormal`: for distinct primes the
cores `O_p(G)` and `O_q(G)` are normal with coprime orders, hence disjoint, hence commute
elementwise (`Subgroup.commute_of_normal_of_disjoint`). So `F(G)` is the range of
`Subgroup.noncommPiCoprod` out of the finite product `∀ p, O_p(G)` of nilpotent `p`-groups,
and nilpotency transfers along that surjection.

Maximality (`Subgroup.le_fittingSubgroup`) rests on
`ConjAct.normal_of_characteristic_of_normal`: a normal nilpotent `H` is the join of its own
`p`-cores, each of which is characteristic in `H` and so normal in `G`, hence a normal
`p`-subgroup of `G` landing in `O_p(G) ≤ F(G)`.
-/

@[expose] public section

namespace Subgroup

variable (p : ℕ) (G : Type*) [Group G]

/-- The `p`-core `O_p(G)`: the supremum of all normal `p`-subgroups of `G`.

By `Subgroup.isPGroup_pCore` this is itself a `p`-group, so it is the largest normal
`p`-subgroup of `G`. -/
def pCore : Subgroup G := sSup {H : Subgroup G | H.Normal ∧ IsPGroup p H}

instance pCore_normal : (pCore p G).Normal :=
  show Subgroup.Normal (sSup {H : Subgroup G | H.Normal ∧ IsPGroup p H}) from
    sSup_normal _ fun _ hH => hH.1

/-- The `p`-core is a `p`-group: a supremum of normal `p`-subgroups is a `p`-group. -/
theorem isPGroup_pCore : IsPGroup p (pCore p G) :=
  show IsPGroup p (sSup {H : Subgroup G | H.Normal ∧ IsPGroup p H} : Subgroup G) from
    Sylow.sSup_of_normal _ (fun _ hH => hH.2) (fun _ hH => hH.1)

variable {p G}

/-- The `p`-core contains every normal `p`-subgroup. -/
theorem le_pCore {H : Subgroup G} (hn : H.Normal) (hp : IsPGroup p H) : H ≤ pCore p G :=
  le_sSup ⟨hn, hp⟩

/-- For distinct primes the `p`-core and the `q`-core are disjoint, their orders being
coprime. -/
theorem disjoint_pCore {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    Disjoint (pCore p G) (pCore q G) :=
  IsPGroup.disjoint_of_ne p q hpq _ _ (isPGroup_pCore p G) (isPGroup_pCore q G)

/-- Elements of `O_p(G)` and `O_q(G)` commute when `p ≠ q`: the cores are normal and
disjoint. -/
theorem commute_pCore {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) {x y : G}
    (hx : x ∈ pCore p G) (hy : y ∈ pCore q G) : Commute x y :=
  commute_of_normal_of_disjoint _ _ (pCore_normal p G) (pCore_normal q G)
    (disjoint_pCore hpq) x y hx hy

/-- The `p`-core is characteristic: any automorphism carries a normal `p`-subgroup to a
normal `p`-subgroup. -/
instance pCore_characteristic (p : ℕ) (G : Type*) [Group G] : (pCore p G).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ
  exact le_pCore ((pCore_normal p G).map φ.toMonoidHom φ.surjective)
    ((isPGroup_pCore p G).map φ.toMonoidHom)

/-- The **Fitting subgroup** `F(G)`, as the join of the `p`-cores of `G` over the prime
factors of `|G|`. For a finite group this is the largest normal nilpotent subgroup, see
`Subgroup.isNilpotent_fittingSubgroup` and `Subgroup.le_fittingSubgroup`. -/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : (Nat.card G).primeFactors, pCore (p : ℕ) G

instance fittingSubgroup_normal (G : Type*) [Group G] : (fittingSubgroup G).Normal :=
  show Subgroup.Normal (⨆ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) from
    iSup_normal _

/-- Each `p`-core, for `p` a prime factor of `|G|`, sits inside the Fitting subgroup. -/
theorem pCore_le_fittingSubgroup {G : Type*} [Group G] {p : ℕ}
    (hp : p ∈ (Nat.card G).primeFactors) : pCore p G ≤ fittingSubgroup G :=
  le_iSup (fun q : (Nat.card G).primeFactors => pCore (q : ℕ) G) ⟨p, hp⟩

/-- **The Fitting subgroup of a finite group is nilpotent.** -/
theorem isNilpotent_fittingSubgroup (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (fittingSubgroup G) := by
  have hfact : ∀ p : (Nat.card G).primeFactors, Fact (p : ℕ).Prime :=
    fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hcomm : Pairwise fun i j : (Nat.card G).primeFactors =>
      ∀ x y : G, x ∈ pCore (i : ℕ) G → y ∈ pCore (j : ℕ) G → Commute x y := by
    intro i j hij x y hx hy
    have := hfact i
    have := hfact j
    exact commute_pCore (fun h => hij (Subtype.ext h)) hx hy
  have : ∀ p : (Nat.card G).primeFactors, Group.IsNilpotent (pCore (p : ℕ) G) := by
    intro p
    have := hfact p
    exact (isPGroup_pCore (p : ℕ) G).isNilpotent
  have hrange : (Subgroup.noncommPiCoprod hcomm).range = fittingSubgroup G :=
    Subgroup.noncommPiCoprod_range
  rw [← hrange]
  exact Group.nilpotent_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

/-- A finite nilpotent group is exhausted by its `p`-cores: `F(G) = ⊤`.

For each prime factor `p` of `|G|` the Sylow `p`-subgroup is normal, hence lies in
`O_p(G)`; so `|G|` and `|F(G)|` have the same `p`-adic valuation for every `p`. -/
theorem fittingSubgroup_eq_top_of_isNilpotent (G : Type*) [Group G] [Finite G]
    [Group.IsNilpotent G] : fittingSubgroup G = ⊤ := by
  refine eq_top_of_card_eq _ (Nat.dvd_antisymm (card_subgroup_dvd_card _) ?_)
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_def]
  intro p
  by_cases hp : p ∈ (Nat.card G).primeFactors
  · have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hle : ((default : Sylow p G) : Subgroup G) ≤ fittingSubgroup G :=
      (le_pCore inferInstance (default : Sylow p G).isPGroup).trans
        (pCore_le_fittingSubgroup hp)
    refine (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp ?_
    rw [← (default : Sylow p G).card_eq_multiplicity]
    exact card_dvd_of_le hle
  · have hz : (Nat.card G).factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hp
    rw [hz]
    exact Nat.zero_le _

/-- **A finite group is nilpotent exactly when its Fitting subgroup is everything.** -/
theorem isNilpotent_iff_fittingSubgroup_eq_top (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent G ↔ fittingSubgroup G = ⊤ := by
  refine ⟨fun _ => fittingSubgroup_eq_top_of_isNilpotent G, fun h => ?_⟩
  have hn := isNilpotent_fittingSubgroup G
  rw [h] at hn
  exact Group.nilpotent_of_mulEquiv topEquiv

/-- **The Fitting subgroup contains every normal nilpotent subgroup**, hence is the largest
one — which justifies the name.

A normal nilpotent `H` is exhausted by its own `p`-cores
(`Subgroup.fittingSubgroup_eq_top_of_isNilpotent`), each of which is characteristic in `H`
and so normal in `G` (`ConjAct.normal_of_characteristic_of_normal`); being a normal
`p`-subgroup of `G` it lands in `O_p(G) ≤ F(G)`. -/
theorem le_fittingSubgroup {G : Type*} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    [Group.IsNilpotent H] : H ≤ fittingSubgroup G := by
  intro x hx
  have hmem : (⟨x, hx⟩ : H) ∈ ⨆ q : (Nat.card H).primeFactors, pCore (q : ℕ) H := by
    show (⟨x, hx⟩ : H) ∈ fittingSubgroup H
    rw [fittingSubgroup_eq_top_of_isNilpotent H]
    exact mem_top _
  refine Subgroup.iSup_induction (C := fun y : H => (y : G) ∈ fittingSubgroup G) _ hmem
    (fun q y hy => ?_) (by simp) (fun a b ha hb => by simpa using mul_mem ha hb)
  have hq : (q : ℕ) ∈ (Nat.card G).primeFactors :=
    Nat.primeFactors_mono (card_subgroup_dvd_card H) Nat.card_pos.ne' q.2
  exact (le_pCore inferInstance ((isPGroup_pCore (q : ℕ) H).map H.subtype)).trans
    (pCore_le_fittingSubgroup hq) (mem_map_of_mem _ hy)

end Subgroup
