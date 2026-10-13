/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.Algebra.Homology.HomTensorDegreewise
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Sheaf.Algebra.Homology.HomTensorDifferential
import Sheaf.Algebra.Homology.HomComplexGlobalCochains
import Sheaf.Algebra.Homology.HomComplexProjections

/-! # Component-normalized tensor-Hom equivalence on homotopy classes
Source: Stacks Project, Cohomology on Sites, Tag 0A90.
(blueprint: lem-pc-normalized-homotopy-tensor-hom).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Uncurrying induces a bijection on homotopy classes, with the actual component formula.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-homotopy-tensor-hom).

Proof: use the degreewise isomorphisms `homTensorDegreewiseMap_spec` between the
iterated sheaf Hom complex and the Hom complex from the total tensor. Their
compatibility with differentials (`homTensorDegreewiseMap_comm`) makes them an
isomorphism of complexes. Construct the global-cochain comparisons on both sides
as in the proof of `homComplex_global_cochains`: use the product projections
specified by `Classical.choose_spec (homComplex_exists (R := X.sheaf))`
(the product specification exposed by `homComplex_projections_exists`), then
the internal-Hom sections equivalence on each factor. In particular, the component
of the comparison applied to s is
the morphism corresponding to s followed by the chosen product projection.
This component formula is needed; an arbitrary witness of the existential
statement `homComplex_global_cochains` does not supply normalization. The
product universal property gives the inverse comparison, and the differential
projection formula shows that these additive equivalences preserve the external
cochain differential. Hence they carry degree-zero cocycles to cocycles and degree-minus-one
boundaries to boundaries, in both directions. Chain maps are degree-zero cocycles;
the relation of differing by such a boundary is exactly chain homotopy. Passing
to these quotients therefore gives the displayed equivalence. For a chain map φ,
its image cocycle gives ψ. The degreewise pure-tensor specification says that the
restriction of ψ to P^p tensor L^q evaluates φ^p at the Hom projection indexed by
q and q+p. The sheaf tensor-Hom adjunction, preceded by symmetry, is exactly
the displayed uncurrying morphism. Equality before sheafification follows on pure
tensors; the tensor and sheafification universal properties imply the displayed
sheaf-morphism equation. This proves the normalization for every representative.
No flatness or injectivity is needed. If one input is zero both Hom sets are
singletons; unbounded inputs cause no difficulty because Hom uses products and
the total tensor uses coproducts. -/
theorem exists_normalizedHomotopyTensorHom (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
    ∃ e : (q.obj P ⟶ q.obj (homComplex (R := X.sheaf) L I)) ≃
        (q.obj (pullbackTensorTotal X P L) ⟶ q.obj I),
      ∀ φ : P ⟶ homComplex (R := X.sheaf) L I,
        ∃ ψ : pullbackTensorTotal X P L ⟶ I,
          (∀ (p r n : ℤ) (h : p + r = n) (h' : r + p = n),
            HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p r n h ≫
              ψ.f n =
              (β_ (P.X p) (L.X r)).hom ≫
                (SheafOfModules.tensorHomEquiv (L.X r) (P.X p) (I.X n)).symm
                  (φ.f p ≫ homTensorProjection X.sheaf L I p r n h')) ∧
          e (q.map φ) = q.map ψ := by sorry

end AlgebraicGeometry
