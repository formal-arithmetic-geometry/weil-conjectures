/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Sheaf.CategoryTheory.SheafTensorStructure
public import Sheaf.CategoryTheory.RingObjectSheaf
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import Sheaf.Topology.ProfiniteCondensedRing

/-!
# The pro-étale site of a point and commutative condensed rings

Source: the Weil conjectures blueprint, `sec-smooth-purity`,
`sk-def-sp-coefficient-towers/pur713-def-point-site.md`, governing reference §3.1
(blueprint: pur713-def-point-site).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Profinite

/-- A sieve covers the pro-étale point precisely when it contains a finite jointly
surjective family. Objects of `Profinite` are profinite spaces and its arrows are continuous
maps. The displayed existential is surjectivity of the map from the finite disjoint union.
Source: blueprint `pur713-def-point-site.md`, first sentence, governing reference §3.1
(blueprint: pur713-def-point-site).

Proof: by `sk-def-sfb-condensed-ring` the topology is the coherent topology. The coherent
covering-sieve criterion says that a covering sieve contains a finite effective-epimorphic
family. In profinite spaces finite effective-epimorphic families are exactly jointly
surjective families, by `Profinite.effectiveEpiFamily_tfae`. This also includes the empty
family, which covers precisely the empty profinite space. -/
theorem pointSite_covering_iff (S : Profinite.{u}) (R : Sieve S) :
    R ∈ (coherentTopology Profinite.{u}) S ↔
      ∃ (I : Type) (_ : Finite I) (T : I → Profinite.{u}) (f : ∀ i, T i ⟶ S),
        (∀ s : S, ∃ (i : I) (t : T i), f i t = s) ∧ ∀ i, R (f i) := by
  sorry

/-- The canonical passage from sheaves of commutative rings on the pro-étale point to
commutative ring objects in abelian sheaves with the sheafified integer tensor.

The source is exactly the category of condensed rings in this node. On objects, forget to
a ring sheaf and use `Sheaf.monObj_sheafCompose_obj`: its multiplication and integer unit
are transported from sheafification along the counit, and commute because all section rings
do. On arrows use the underlying additive sheaf map, with the upstream `IsMonHom` instance.
The monoidal and symmetric structures are exactly `sfbSheafTensorStructure` specialized to
this site and the integer tensor on `Ab`, not the cartesian monoidal structure.

Source: blueprint `pur713-def-point-site.md`, second sentence, governing reference §3.1
(blueprint: pur713-def-point-site). -/
noncomputable def commRingSheafToCommMon :
    Sheaf (coherentTopology Profinite.{u}) CommRingCat.{max u v + 1} ⥤
      @CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{max u v + 1}) _
        (sfbSheafTensorStructure (A := Ab.{max u v + 1})
          (coherentTopology Profinite.{u})).monoidal
        (sfbSheafTensorStructure (A := Ab.{max u v + 1})
          (coherentTopology Profinite.{u})).symmetric.toBraidedCategory := by
  let J := coherentTopology Profinite.{u}
  let t := sfbSheafTensorStructure (A := Ab.{max u v + 1}) J
  letI : MonoidalCategory (Sheaf J Ab.{max u v + 1}) := t.monoidal
  letI : SymmetricCategory (Sheaf J Ab.{max u v + 1}) := t.symmetric
  let U := sheafCompose J (forget₂ CommRingCat.{max u v + 1} RingCat.{max u v + 1})
  let V := sheafCompose J (forget₂ RingCat.{max u v + 1} Ab.{max u v + 1})
  exact
    { obj := fun S ↦
        { X := V.obj (U.obj S)
          mon := Sheaf.monObj_sheafCompose_obj J (U.obj S)
          comm := Sheaf.isCommMonObj_sheafCompose_obj J (U.obj S)
            (fun W a b ↦ @mul_comm (S.obj.obj W) inferInstance a b) }
      map := fun f ↦ CommMon.homMk (Mon.Hom.mk (V.map (U.map f))) }

/-- The two descriptions of a commutative condensed ring are equivalent, via the canonical
functor just defined; in particular the equivalence keeps the underlying abelian sheaf.
Source: blueprint `pur713-def-point-site.md`, second sentence, governing reference §3.1
(blueprint: pur713-def-point-site).

Proof, following the node's four steps:
1. Use `def-weil-size-convention` and `sk-def-sfb-condensed-ring` for the bounded profinite
site. Apply `det-def-sfb-sheaf-tensor-structure` with `Ab`: tensor is sheafified objectwise
integer tensor and the unit is the sheafified constant integer presheaf.
2. For a sheaf of commutative rings, `det-def-sfb-ring-object-sheaf` extends multiplication
and the integer unit uniquely to that tensor and unit. The coherence equations give the
`MonObj` and `IsCommMonObj` of `pur713-def-ring-object`; this is our functor on objects.
3. Conversely, for a commutative ring object, restrict multiplication and unit along the
sheafification units (`def-weil-pbc-sheafification`). At S define xy by applying the restricted
multiplication to x tensor y, and define 1 as the restricted unit at the integer 1.
The tensor universal property (`def-weil-pbc-module-tensor-product`) gives both distributive
laws on the existing abelian group, and the additive unit map sends n to n times 1.
Precompose the monoid associativity equation with the iterated tensor comparison from
presheaves: the specified associator reduces it to (xy)z=x(yz). The analogous unit and
symmetry comparisons give 1x=x, x1=x and xy=yx. Naturality makes restrictions unital ring
homomorphisms. Matching families glue uniquely because the underlying abelian presheaf is
a sheaf, so this constructs a sheaf of commutative rings.
4. The extension clauses in `det-def-sfb-ring-object-sheaf` recover the original section
operations. In the opposite direction uniqueness in `def-weil-pbc-sheafification` recovers
the original multiplication and unit. A ring-object morphism is already additive; its two
compatibility equations, restricted along the tensor and unit comparisons, say that each
component preserves products and 1. Thus the constructions are inverse on morphisms too,
and respect identities and composition. Our canonical functor is full, faithful and
essentially surjective, which is exactly `Functor.IsEquivalence`. -/
theorem commRingSheafToCommMon_isEquivalence :
    (commRingSheafToCommMon.{u, v}).IsEquivalence := by
  sorry

end Profinite
