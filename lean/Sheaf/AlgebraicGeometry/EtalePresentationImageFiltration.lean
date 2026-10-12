/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleHypercohomologyFiltration
public import Sheaf.Paper.EtaleTermwiseHypercohomology
/-! # The image predicate and the Cartan--Eilenberg abutment filtration

Source: Stacks Project, Tag 015J.
(blueprint: lem-weil-pbc-etale-presentation-image-filtration).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The presentation's canonical filtration consists of images from complexes supported
above its index. The statement compares filtration membership only, with no page data.
Source: Stacks Project, Tag 015J, the first hypercohomology filtration.

Proof: The presentation's H_formula identifies its step q with the image on cohomology
of the complex-degree q step of the filtered Cartan--Eilenberg total. The latter resolves
the stupid truncation of K in degrees at least q, with its canonical inclusion into K:
restrict the augmentation and use the exact augmented rows and the bounded support
region to see that it is a quasi-isomorphism. The canonical resolution comparison
c_formula identifies its image with the image of the stupid-truncation inclusion under
RΓ. Every map T -> K from a complex zero below q factors through this truncation,
degreewise, and the factorization commutes with the differential. Thus every class in
the predicate belongs to this image. Conversely, the truncation itself is zero below q
and its inclusion supplies the witness T,f,y for every class in this image. These two
inclusions prove the equivalence, including zero objects and all integer indices.
(blueprint: lem-weil-pbc-etale-presentation-image-filtration). -/
theorem etalePresentation_image_filtration
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ)
    (x : (cohomology AddCommGrpCat.{u + 1} X p).obj (DerivedCategory.Q.obj K.obj)) :
    InEtaleHypercohomologyFiltration X K.obj p q x ↔
      ∃ y : ((T.H p).step q : AddCommGrpCat.{u + 1}), ((T.H p).step q).arrow y = x := by
  sorry

end AlgebraicGeometry.Etale
