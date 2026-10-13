/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.HomTensorDifferential
import Sheaf.Algebra.Homology.HomTensorNaturality
import Sheaf.Algebra.Homology.HomComplexGlobalCochains

/-! # Bijectivity of normalized derived tensor-Hom maps
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-canonical-derived-tensor-hom-map-bijective).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Every normalized natural uncurrying map is bijective.
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom), using
sites-cohomology.tex, Tag 0A90 (Hom complexes).
(blueprint: lem-pc-canonical-derived-tensor-hom-map-bijective).
Proof: Reuse `homTensorDegreewiseMap_spec`, `homTensorDegreewiseMap_comm`, and
`homTensorDegreewiseMap_natural` for the normalized degreewise construction,
differential compatibility and functoriality. The global-cochain comparison
`homComplex_global_cochains` identifies chain maps with degree-zero cocycles and
homotopies with degree-minus-one boundaries; hence this comparison gives precisely
the stated map on homotopy classes. The pure-tensor condition in the degreewise
specification agrees with `schemeTensorHomUncurryComponent` by the sheaf tensor-Hom
adjunction and symmetry. Thus these existing lemmas supply the component calculation,
including its normalization, rather than an arbitrary existential isomorphism.
First take K=QP and L=QLc with P,Lc K-flat, and M=QMc. The tensor model
comparison is an isomorphism, and QHom(Lc,I(Mc)) computes derived internal Hom.
Both I(Mc) and Hom(Lc,I(Mc)) are K-injective, so maps to them in the derived category
are homotopy classes of chain maps. Componentwise currying is inverse to the
uncurrying in the representative clause. The sheaf tensor-Hom inverse identities
on every tensor summand prove the two inverse identities for chain maps. The same
calculation for homotopies shows these inverse maps descend to homotopy classes.
Consequently the map prescribed by that clause is injective and surjective on
these representatives. Every derived object has a K-flat representative, and every
target has a complex representative. Naturality with respect to their isomorphisms
conjugates t by bijections of Hom sets. Bijectivity is preserved by these
conjugations, proving the result for arbitrary K,L,M. -/
theorem canonicalDerivedTensorHomMap_bijective (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : IsCanonicalDerivedTensorHomMap X t) :
    ∀ K L M, Function.Bijective (t K L M) := by sorry

end AlgebraicGeometry
