/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.PairHenselization
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.EtaleSectionIdempotentSplitting
import Sheaf.RingTheory.EtaleSectionLiftingOfGabberRoots
import Sheaf.RingTheory.HenselianFactorizationCriterion
import Sheaf.RingTheory.IdempotentsDeterminedModuloRadical

/-!
# Universal property of the henselization of a pair

Source: Stacks Project, More on Algebra, Tag 0A02, last paragraph of the proof
(blueprint: lem-weil-pbc-henselization-universal-property).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The henselization of a pair has the universal property of a henselian pair.
Source: Stacks Project, More on Algebra, Tag 0A02
(blueprint: lem-weil-pbc-henselization-universal-property).

The colimit cocone `c` represents `(Bʰ, Jʰ)`, and `c.pt.hom.hom` is its structural
map `η : B → Bʰ`; the ideal in the colimit is `J.map c.pt.hom.hom`. For a henselian
pair `(A', I')` and a map `φ` carrying `J` into `I'`, the displayed existential gives
the unique factorization and records that the factorization carries `Jʰ` into `I'`.

Proof: use the sections of `A' ⊗[B] C` supplied by the Gabber root criterion for each
étale stage, prove their uniqueness by the idempotent splitting of the diagonal and
idempotents modulo the Jacobson radical, and pass to the colimit. The colimit
universal property gives existence and uniqueness; `Jʰ = JBʰ` gives the ideal inclusion.

Proof steps from the blueprint: (1) use the identity object and the colimit cocone to
identify the structural map with the coprojection of `B`; (2) obtain the
Jacobson-radical and root-lifting conditions from `HenselianRing` via
`lem-weil-pbc-henselian-factorization-criterion`; (3) for each stage form
`A' ⊗[B] C`, which is étale over `A'` and reduces to `A'/I'`; (4) lift the
reduced section using `lem-weil-pbc-gabber-root-criterion-etale-section-lifting`;
(5) prove uniqueness of each section by the étale diagonal idempotent splitting
and `lem-weil-pbc-idempotents-determined-modulo-radical`; (6) check compatibility
and use the colimit to construct `ψ`; (7) compare any other factorization
stagewise and use the ring-colimit universal property for uniqueness; (8) since
`Jʰ = J Bʰ`, the image of `Jʰ` under `ψ` lies in `I'` by `hφ` and ideal closure.
These steps use `lem-weil-pbc-pair-henselization`, `def-weil-pbc-category-colimit`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-weil-pbc-etale-composition-cancellation`,
`lem-weil-pbc-etale-ring-base-change`, and
`lem-weil-pbc-etale-section-idempotent-splitting` as cited by the node.
-/
theorem henselization_universal_property (B : Type u) [CommRing B] (J : Ideal B)
    (c : Cocone (ObjectProperty.ι (fun C : Under (CommRingCat.of B) ↦
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
          (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c))
    (A' : Type u) [CommRing A'] (I' : Ideal A') [HenselianRing A' I']
    (φ : B →+* A') (hφ : J.map φ ≤ I') :
    ∃ ψ : c.pt.right →+* A',
      RingHom.comp ψ (CommRingCat.Hom.hom c.pt.hom) = φ ∧
        (J.map (CommRingCat.Hom.hom c.pt.hom)).map ψ ≤ I' ∧
        ∀ ψ' : c.pt.right →+* A', RingHom.comp ψ' (CommRingCat.Hom.hom c.pt.hom) = φ → ψ' = ψ := by
  sorry

end RingTheory
