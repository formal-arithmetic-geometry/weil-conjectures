/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.TraceFormula.SectionProjEtaleEmbedding
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Ordinary ampleness from an everywhere-defined canonical section-Proj embedding

Source: Stacks Project, Morphisms, Tag 01VJ, (5) implies (1); Descent on Spaces,
Tag 0D3C, final paragraph (blueprint: lem-trf-section-proj-embedding-ordinary-ample).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The reverse canonical-Proj criterion on a representing scheme, with transport along
an identified etale pullback. This statement assumes an existing global open canonical
embedding and has no cover or local-ampleness hypotheses.

Source: Stacks, Morphisms, Tag 01VJ, (5) implies (1); Descent on Spaces, Tag 0D3C,
final paragraph; Descent, Tag 03LC
(blueprint: lem-trf-section-proj-embedding-ordinary-ample).

Proof: transport f to p on U using e. Scheme tests of the quasi-compactness hypothesis
give quasi-compactness of p. The separated diagonal hypothesis transports to a closed
scheme diagonal, hence p is quasi-separated. The cartesian realization identifies its
ordinary invertible module H with schemeRestriction X at e. The AgreesWithSchemes
condition identifies every homogeneous degree with the ordinary direct image of H^n,
including products, unit and restrictions. Transport degreeIso to construct the ordinary
RelativeSectionAlgebra. The evaluation equation identifies its evaluation with tensor
unit insertion; the generation and canonical-map conditions consequently give the
ordinary everywhere generation and canonical map. Representable open immersion of r
gives an open immersion of the represented scheme map. Apply the reverse scheme
canonical-Proj criterion to obtain relative ampleness of H. Finally z and composition
of etale restriction identify H with the Zariski restriction of M along e followed by k.
On each inverse-image open apply restriction to that isomorphism and use invariance of
invertibility and ampleness under isomorphism. The open-immersion restriction/tensor
comparison changes tensor pullback to the literal restrictFunctor in the conclusion.
These comparisons preserve all opens and include the empty scheme.
-/
theorem ordinary_ample_of_sectionProj_embedding
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hqc : IsQuasiCompactPresheafMap f) (hsep : IsSeparatedPresheafMap f)
    (L : X.Modules) (hL : X.IsLineModule L)
    (A : SectionProjModel f (lineTestFamily X L hL))
    (hagrees : A.sections.AgreesWithSchemes)
    (hgen : A.evaluation.IsGenerationOpen ⊤)
    (r : X.obj.obj ⟶ yoneda.obj (projOver T A.affine))
    (hcanonical : A.evaluation.IsCanonicalMap ⊤ ((⊤ : Subfunctor X.obj.obj).ι ≫ r))
    (hopen : IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) r)
    (U : Over S) (e : yoneda.obj U ≅ X.obj.obj) (he : IsEtale e.hom)
    (p : U ⟶ T) (hp : yoneda.map p = e.hom ≫ f)
    (F : AlgebraicSpace S) (k : X ⟶ F) (hk : IsEtale k.hom.hom)
    (M : F.Modules) (z : L ≅ (pullback k hk).obj M) :
    ∀ W : T.left.Opens, IsAffineOpen W →
      ∃ h : ((Scheme.Modules.restrictFunctor (p.left ⁻¹ᵁ W).ι).obj
          ((F.schemeRestriction
            ⟨CostructuredArrow.mk (e.hom ≫ k.hom.hom),
              isEtale_comp _ _ he hk⟩).obj M)).IsInvertible,
        @Scheme.Modules.IsAmple (p.left ⁻¹ᵁ W).toScheme
          ((Scheme.Modules.restrictFunctor (p.left ⁻¹ᵁ W).ι).obj
            ((F.schemeRestriction
              ⟨CostructuredArrow.mk (e.hom ≫ k.hom.hom), isEtale_comp _ _ he hk⟩).obj M))
          h := by sorry

end AlgebraicGeometry.AlgebraicSpace
