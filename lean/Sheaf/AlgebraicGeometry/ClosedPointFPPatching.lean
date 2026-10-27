module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap
import WeilConjectures.AlgebraicGeometry.OverPullbackDiagonalClosedImmersion
import Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion

/-!
# Finite-presentation patching at a closed point

Source: Stacks Project, Limits, Tags 0BPA and 0EY3; smooth/open/closed descent
uses Tags 0C0C, 0EUU and 01ZP.
(blueprint: lem-sfb-closed-point-fp-patching)

The equivalence is stated as essential surjectivity and full faithfulness,
including compatibility with the prescribed overlap isomorphism. The overlap
is the fibre product U ×_S T, canonically the punctured local spectrum V.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical comparison between the two iterated restrictions to U ×_S T.

Source: Stacks Project, Limits, Tag 0BPA, the restriction functor and its
cartesian overlap squares.
(blueprint: lem-sfb-closed-point-fp-patching)

This is the composite of Mathlib's pullback-composition isomorphisms and the
transport along the defining equation of the base pullback square.
-/
def overPullbackOverlapIso {S U T : Scheme.{u}} (i : U ⟶ S) (j : T ⟶ S)
    (X : Over S) :
    (Over.pullback (pullback.fst i j)).obj ((Over.pullback i).obj X) ≅
      (Over.pullback (pullback.snd i j)).obj ((Over.pullback j).obj X) :=
  ((Over.pullbackComp (pullback.fst i j) i).app X).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj X)
      (pullback.condition (f := i) (g := j))) ≪≫
    (Over.pullbackComp (pullback.snd i j) j).app X

/-- Finite-presentation schemes and their arrows patch across a closed point,
and smoothness, separatedness, and open/closed immersions are detected there.

Source: Stacks Project, Limits, Tag 0BPA, with property detection as in
Tag 0EY3 using Tags 0C0C, 01ZQ, 0EUU and 01ZP.
(blueprint: lem-sfb-closed-point-fp-patching)

Proof:
1. Use the directed set of affine open neighbourhoods W of s, ordered by shrinking. Since D is
   Noetherian, S is locally Noetherian by its one affine chart, and is quasi-compact and quasi-
   separated by the affine-scheme lemma. Thus S is Noetherian. Every W and W\cap U is Noetherian
   by the open-subscheme lemma, and hence quasi-compact and quasi-separated. The local-ring
   canonical-morphism lemma identifies \operatorname{Spec}\mathcal O_{S,s} with
   T=\operatorname{Spec}D_{\mathfrak m}. The affine-neighbourhood limit lemma gives
   T=\varprojlim_W W with affine transitions. The only prime of D_{\mathfrak m} contracting to
   \mathfrak m is \mathfrak mD_{\mathfrak m}: such a prime contains this maximal ideal and hence
   equals it. Consequently T\times_SU=V. Apply the open-restriction clause of the affine-
   transition limit lemma to obtain V=\varprojlim_W(W\cap U) with affine transitions; pullback by
   an open subscheme is the corresponding inverse-image open. All indexing sets here are sets of
   opens of the fixed space S, so they are small.
   Uses: pqf-def-locnoeth, lem-weil-pbc-affine-scheme-qcqs,
     lem-weil-pbc-noetherian-open-subscheme-noetherian,
     lem-weil-pbc-locally-noetherian-quasi-separated,
     lem-weil-pbc-spec-local-ring-canonical-morphism,
     lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods, lem-weil-pbc-limit-affine-transition,
     lem-weil-pbc-open-preimage-fibre-product.
2. Given (X_U,X_T,\alpha), apply clause (1) of finite-presentation spreading to T=\varprojlim W:
   choose W_0 and X_0\to W_0 of finite presentation with (X_0)_T\simeq X_T. For W\subseteq W_0,
   both (X_U)_{W\cap U} and (X_0)_{W\cap U} have finite presentation by base-change permanence. At
   the limit V, the given \alpha and its inverse are arrows between these two fixed models. Apply
   clause (2) of spreading twice to the system (W\cap U), then take a common smaller neighbourhood
   to obtain arrows b and c lifting \alpha and \alpha^{-1}. Apply clause (3) to cb and the
   identity, and to bc and the identity. After a common further shrinking both identities hold. We
   have obtained an isomorphism \beta:(X_U)_{W\cap U}\simeq(X_0)_ {W\cap U} whose restriction to V
   is the prescribed \alpha.
   Uses: thm-pd-spreading-out, lem-weil-pbc-qcqs-morphism-permanence.
3. Now S=U\cup W. Apply relative Zariski gluing to X_U\to U and X_W=(X_0)_W\to W, with transition
   \beta on U\cap W. For a two-member covering the self transitions are identities and the two
   distinct transitions are \beta and \beta^{-1}, so the cocycle equations are exactly the inverse
   identities already imposed. The gluing lemma gives an S-scheme X restricting to X_U and X_W
   compatibly with \beta. Its restriction to T is X_T, because T\to S factors through W; its
   induced overlap identification is the given \alpha.
   Uses: lem-galois-glue, lem-weil-pbc-spec-local-ring-canonical-morphism.
4. Check that this glued X\to S has finite presentation, rather than only gluing its underlying
   schemes. The finite-presentation-at-a-point charts for X_U\to U and X_W\to W are also charts
   for X\to S: an affine open in either base open is an affine open in S. This gives local finite
   presentation by its definition, and, by the affine-open finite-presentation lemma, finite
   polynomial presentations on every affine chart; forgetting their relations gives local finite
   type. Since U,W are quasi-compact and the two structure maps are quasi-compact, X_U,X_W are
   quasi-compact by qcqs permanence. Their union X is quasi-compact (combine finite subcovers on
   the two pieces), and the same permanence lemma makes X\to S quasi-compact since S is quasi-
   separated. Thus X\to S is of finite type. The finite-type-over-Noetherian lemma makes X
   Noetherian. In particular X is quasi-separated, and qcqs permanence makes X\to S quasi-
   separated. Together with local finite presentation this proves X\in\mathrm{FP}(S). This proves
   essential surjectivity. Base-change permanence also ensures that restriction defines the stated
   functor on every object of \mathrm{FP}(S).
   Uses: def-sbc-locally-finite-presentation, def-weil-finite-type-morphism,
     lem-weil-pbc-lfp-affine-opens-finite-presentation, lem-weil-pbc-qcqs-morphism-permanence,
     lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated.
5. For full faithfulness fix X,Y\in\mathrm{FP}(S) and a compatible pair a_U:X_U\to Y_U, a_T:X_T\to
   Y_T. Restrict the fixed global models to the affine neighbourhoods W. Clause (2) of spreading
   over T=\varprojlim W gives a lift a_W:X_W\to Y_W of a_T after shrinking W. On W\cap U the
   arrows a_W and a_U have equal base change to V, by compatibility of the pair. Clause (3) of
   spreading over V=\varprojlim(W\cap U) makes them equal after shrinking W again. Their source
   and target models have finite presentation by base-change permanence. Glue a_U and a_W by the
   scheme-morphism gluing lemma. Their composites with Y\to S equal X\to S on this open covering,
   so uniqueness of gluing makes the resulting map an S-map. Its pullback to T is a_T. Conversely,
   if two global S-maps have equal restrictions to U and T, clause (3) for the system W makes them
   equal on one smaller W, and they are equal on U already. Uniqueness in morphism gluing makes
   them equal on X. Thus every compatible pair lifts to exactly one arrow, proving the claimed
   equivalence.
   Uses: thm-pd-spreading-out, lem-weil-pbc-qcqs-morphism-permanence,
     lem-weil-pbc-scheme-morphism-gluing.
6. For the detection clauses keep the same directed neighbourhood system and start from the fixed
   global finite-presentation schemes. The affine stages W are qcqs, and X_W,Y_W are qcqs by qcqs
   permanence. Their structure maps are locally of finite presentation. Any arrow a:X\to Y over S
   is locally of finite presentation by the over-base finite-presentation lemma: X\to S is locally
   of finite presentation and Y\to S is locally of finite type (forget the relations in its finite
   polynomial presentations). Its restrictions a_W are locally of finite presentation by base-
   change permanence, and in particular locally of finite type. Thus the local-finite-presentation
   hypothesis for smooth/open-immersion descent and the local-finite-type hypothesis for closed-
   immersion descent are available. Separated descent needs no finiteness hypothesis on the arrow.
   None of these applications requires X or Y to be separated.
   Uses: lem-weil-pbc-qcqs-morphism-permanence, lem-a1-map-over-base-finite-presentation,
     def-sbc-locally-finite-presentation.
7. Suppose X_T\to T is smooth. Apply smooth descent to X_W\to W and T=\varprojlim W to obtain an
   affine neighbourhood W over which X_W\to W is smooth. If X_U\to U is also smooth, the open-
   restriction smoothness lemma (its composition-with-the-base-open clause) makes X_U\to S and
   X_W\to S smooth. Smoothness on an open cover of the source then makes X\to S smooth, as
   X=X_U\cup X_W. Conversely smooth base change gives smoothness of both X_U\to U and X_T\to T.
   Uses: lem-weil-pbc-descend-smooth-qcqs, lem-weil-pbc-smooth-restrict-open-subschemes,
     lem-weil-pbc-smooth-local-on-source, lem-pc-proper-base-change.
8. Suppose X_T\to T is separated. Apply separated descent to the structure morphisms X_W\to W,
   taking the target model to be W itself, to get a neighbourhood W with X_W\to W separated. If
   X_U\to U is separated too, the base-changed-diagonal criterion says that the restrictions of
   \Delta:X\to X\times_SX over U and W are closed immersions. These are restrictions over the open
   cover (X\times_SX)_U\cup(X\times_SX)_W=X\times_SX. The closed-immersion target-locality lemma
   makes \Delta a closed immersion, hence X\to S separated. Conversely, if \Delta is closed, its
   base changes along U\to S and T\to S are closed by closed-immersion base change; the same
   diagonal criterion gives separatedness of the two restrictions.
   Uses: lem-weil-pbc-descend-separated, lem-weil-pbc-over-pullback-diagonal-closed-immersion,
     lem-weil-pbc-closed-finite-etale-zariski-local, lem-weil-pbc-closed-immersion-base-change.
9. Let a:X\to Y be the arrow of the statement. If a_T is an open immersion, apply open-immersion
   descent to the fixed arrows a_W:X_W\to Y_W to obtain a neighbourhood W on which a_W is an open
   immersion. If instead a_T is a closed immersion, apply closed-immersion descent to obtain W on
   which a_W is a closed immersion. The qcqs and local finite presentation/type hypotheses were
   verified in step 6. Thus in either case the local restriction on T has been replaced by a
   restriction on an actual open neighbourhood W of s.
   Uses: lem-weil-pbc-descend-open-immersion-qcqs, lem-weil-pbc-descend-closed-immersion.
10. The target opens Y_U,Y_W cover Y, and their inverse images under the S-arrow a are exactly
   X_U,X_W. If a_U and a_W are closed immersions, target locality of closed immersions therefore
   makes a a closed immersion. Conversely both a_U and a_T are closed immersions when a is one, by
   closed-immersion base change.
   Uses: lem-weil-pbc-closed-finite-etale-zariski-local, lem-weil-pbc-closed-immersion-base-change.
11. If a_U and a_W are open immersions, their open images together form the image of a, which is
   open in Y. The map a is injective: two points over the same y both lie over any one of Y_U,Y_W
   containing y, and the restriction there is injective. On these target opens a has continuous
   inverse onto its image and induces an isomorphism of structure sheaves. The inverses and the
   sheaf isomorphisms agree on intersections because they are inverses to the same map. Hence a is
   an isomorphism onto that open image, which is precisely the definition of open immersion.
   Conversely open-immersion base change gives both a_U and a_T when a is an open immersion.
   Uses: def-weil-open-immersion, lem-weil-pbc-open-immersion-base-change.

The first conjunct is essential surjectivity, the second is full faithfulness;
together they assert that the restriction functor is an equivalence. The third
and fourth conjuncts are precisely the four property-detection equivalences.
The binder hU specifies the already named complement open; it is not an
additional geometric restriction. No separatedness of the objects is assumed.
-/
theorem finitePresentation_closedPoint_patching
    (D : Type u) [CommRing D] [IsNoetherianRing D]
    (m : Ideal D) [m.IsMaximal]
    (U : (Spec (CommRingCat.of D)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of D))) =
      {⟨m, inferInstance⟩}ᶜ) :
    (∀ (XU : Over U.toScheme) (XT : Over (Spec (.of (Localization.AtPrime m)))),
      (LocallyOfFinitePresentation XU.hom ∧ QuasiCompact XU.hom ∧ QuasiSeparated XU.hom) →
      (LocallyOfFinitePresentation XT.hom ∧ QuasiCompact XT.hom ∧ QuasiSeparated XT.hom) →
      ∀ α : (Over.pullback (pullback.fst U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
        (Localization.AtPrime m)))))).obj XU ≅
        (Over.pullback (pullback.snd U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
          (Localization.AtPrime m)))))).obj XT,
      ∃ X : Over (Spec (.of D)),
        (LocallyOfFinitePresentation X.hom ∧ QuasiCompact X.hom ∧ QuasiSeparated X.hom) ∧
        ∃ (eU : (Over.pullback U.ι).obj X ≅ XU)
          (eT : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime
            m))))).obj X ≅ XT),
          (Over.pullback (pullback.fst U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
            (Localization.AtPrime m)))))).map eU.hom ≫ α.hom =
            (overPullbackOverlapIso U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
              (Localization.AtPrime m)))) X).hom ≫
              (Over.pullback (pullback.snd U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
                (Localization.AtPrime m)))))).map eT.hom) ∧
    (∀ (X Y : Over (Spec (.of D))),
      (LocallyOfFinitePresentation X.hom ∧ QuasiCompact X.hom ∧ QuasiSeparated X.hom) →
      (LocallyOfFinitePresentation Y.hom ∧ QuasiCompact Y.hom ∧ QuasiSeparated Y.hom) →
      ∀ (aU : (Over.pullback U.ι).obj X ⟶ (Over.pullback U.ι).obj Y)
        (aT : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime
          m))))).obj X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D
          (Localization.AtPrime m))))).obj Y),
        (Over.pullback (pullback.fst U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
          (Localization.AtPrime m)))))).map aU ≫
            (overPullbackOverlapIso U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
              (Localization.AtPrime m)))) Y).hom =
          (overPullbackOverlapIso U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
            (Localization.AtPrime m)))) X).hom ≫
            (Over.pullback (pullback.snd U.ι (Spec.map (CommRingCat.ofHom (algebraMap D
              (Localization.AtPrime m)))))).map aT →
        ∃! a : X ⟶ Y, (Over.pullback U.ι).map a = aU ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime m))))).map
            a = aT) ∧
    (∀ X : Over (Spec (.of D)),
      (LocallyOfFinitePresentation X.hom ∧ QuasiCompact X.hom ∧ QuasiSeparated X.hom) →
      (Smooth X.hom ↔ Smooth ((Over.pullback U.ι).obj X).hom ∧
        Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime
          m))))).obj X).hom) ∧
      (IsSeparated X.hom ↔ IsSeparated ((Over.pullback U.ι).obj X).hom ∧
        IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime
          m))))).obj X).hom)) ∧
    (∀ (X Y : Over (Spec (.of D))),
      (LocallyOfFinitePresentation X.hom ∧ QuasiCompact X.hom ∧ QuasiSeparated X.hom) →
      (LocallyOfFinitePresentation Y.hom ∧ QuasiCompact Y.hom ∧ QuasiSeparated Y.hom) →
      ∀ a : X ⟶ Y,
      (IsOpenImmersion a.left ↔ IsOpenImmersion ((Over.pullback U.ι).map a).left ∧
        IsOpenImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D
          (Localization.AtPrime m))))).map a).left) ∧
      (IsClosedImmersion a.left ↔ IsClosedImmersion ((Over.pullback U.ι).map a).left ∧
        IsClosedImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D
          (Localization.AtPrime m))))).map a).left)) := by
  sorry

end AlgebraicGeometry
