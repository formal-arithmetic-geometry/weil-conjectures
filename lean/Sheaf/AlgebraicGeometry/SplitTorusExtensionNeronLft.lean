module

public import Sheaf.AlgebraicGeometry.NeronLftModel
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.AlgebraicGeometry.SplitTorusCharacterPushout

/-!
# Néron lft-models of split-torus extensions

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 10.1 Proposition 7,
pp.292--293 (blueprint: lem-sfb-split-torus-extension-neron-lft).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A geometrically connected commutative extension by a split torus admits a Néron
lft-model if its character-free quotient does.
Source: BLR, 10.1 Proposition 7, pp.292--293
(blueprint: lem-sfb-split-torus-extension-neron-lft).

Proof plan:
1. Local lifting makes H geometrically connected. The Néron mapping property makes
   its model commutative. Apply lem-sfb-neron-neutral-local-properties to its neutral
   finite-type open subgroup Q and to localizations of the base.
2. Apply lem-sfb-split-torus-character-pushout to each coordinate character. The
   resulting frame bundles carry primitive line data, and their product over H
   recovers G by fppf descent. For rank zero this is the identification G = H.
3. Apply lem-sfb-multiplicative-line-dedekind-extension to extend those lines over Q.
   Their frame product is a smooth separated commutative connected-fibre finite-type
   group B whose generic fibre is the given extension G.
4. By lem-sc-dedekind-localization-dvr the local rings at maximal ideals are DVRs.
   Apply lem-sfb-split-torus-translate-hull locally, using the given vanishing of
   characters of H. It constructs separated smooth commutative lft models with open
   identity subgroup B and lifting over every essentially smooth local DVR extension.
5. Apply lem-sfb-neron-dvr-point-criterion to these local models to obtain the full
   Néron mapping property on each localization, not merely lifting of étale points.
6. Apply lem-sfb-neron-connected-model-globalization with the common connected model
   B to glue the local models and obtain the full mapping property over Spec D. -/
theorem neron_lft_of_splitTorus_extension
    (D E : Type u) [CommRing D] [IsDedekindDomain D]
    (_hdim : ringKrullDim D = 1) [Field E] [Algebra D E] [IsFractionRing D E]
    (r : ℕ) (G H : Grp (Over (Spec (.of E))))
    [IsCommMonObj G.X] [IsCommMonObj H.X]
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsClosedImmersion (pullback.diagonal G.X.hom)]
    [IsClosedImmersion (pullback.diagonal H.X.hom)]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [GeometricallyConnected G.X.hom]
    (i : MultiplicativeType.splitTorus E r ⟶ G) (q : G ⟶ H)
    (_hkernel : IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus E r).X)
      q.hom.hom η[H.X])
    (_hlocallySurjective : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (.of E))) (yoneda.map q.hom.hom))
    (_hcharacters : ∀ f : H.X ⟶ StandardGroupSchemes.multiplicative E,
      IsMonHom f → f = 1)
    (_hmodel : ∃ N : Grp (Over (Spec (.of D))),
      ∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).mapGrp.obj N ≅ H,
        IsNeronLftModel N H e) :
    ∃ N : Grp (Over (Spec (.of D))), IsCommMonObj N.X ∧
      ∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).mapGrp.obj N ≅ G,
        IsNeronLftModel N G e := by
  sorry

end AlgebraicGeometry
