/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent

/-!
# Eventual smoothness in a noetherian approximation

Source: Stacks Project, Tag 0C0C, limits.tex, lemma-descend-smooth.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A finitely presented stage model whose limit base change is smooth becomes smooth
at a later stage of a noetherian approximation.

Source: Stacks Project, Tag 0C0C, limits.tex, lemma-descend-smooth; Tags 0CAQ and
01ZM. Apply 0C0C with
Y equal to the base system.
Proof: restrict the system to Over i; its limit remains S. The noetherian base
stage has a finite affine cover. Quasi-compactness of p gives a finite affine cover
of each inverse image, and p on these charts is finitely presented. Base change of
these covers covers every later stage and the limit. Affine transition maps keep
these base-changed charts affine, and their coordinate rings have the limit rings
as filtered colimits (global-sections continuity). Each limit chart morphism is
smooth because it is a restriction of f. Smooth algebra descent through filtered
colimits (Stacks Tag 0CAQ) gives a smooth model of each limit chart over a later base
chart. Both this model and the original chart model are finitely presented. Descend
the isomorphism between their limit base changes and its inverse by Tag 01ZM(2),
then their two inverse identities by Tag 01ZM(3). Thus the original chart model is
smooth at a later stage too. Choose a common later index for the finitely many charts;
base change preserves smoothness. These charts still cover the stage source and
base, so locality of smoothness proves the assertion. Empty charts and an empty
source are allowed: the same argument applies to the zero ring and empty covers.
This expands the affine-local reduction of Tag 0C0C; alternatively its affine
step is Tag 0C0B, which descends the finitely many identities of a splitting of
the conormal map.

(blueprint: lem-sbc-noetherian-approximation-smooth-stage) -/
theorem Scheme.NoetherianApproximation.exists_smooth_stage {S : Scheme.{u}}
    (N : S.NoetherianApproximation) {i : N.I} {Y X : Scheme.{u}}
    (p : Y ⟶ N.D.obj i) [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p] (f : X ⟶ S) [Smooth f] (a : X ⟶ Y)
    (H : IsPullback a f p (N.π.app i)) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom)) := by sorry

end AlgebraicGeometry
