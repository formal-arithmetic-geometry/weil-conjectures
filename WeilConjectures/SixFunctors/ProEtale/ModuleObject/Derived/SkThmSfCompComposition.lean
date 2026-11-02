/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange

/-!
# Composition and base change for condensed compact supports

Source: current blueprint, sk-thm-sf-comp-composition, clauses (1)--(2) and proof
(blueprint: sk-thm-sf-comp-composition).

The comparisons below are natural isomorphisms on the full ambient localizing closures.
Preservation of the bounded constructible finite-Tor predicates expresses their restriction
there. Every scheme and every arrow of a Cartesian square belongs to `SepFinType k`.
The existing proper/open maps specify the normalization, rather than arbitrary endpoint
isomorphisms. Pasting here means successive changes of the base.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 1024

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactSupportComposition

/-- The two clauses of compact-support composition and base change in the standing setting.

Source: blueprint latest, sk-thm-sf-comp-composition, Proposition, clauses (1)--(2),
composition, canonicity/associativity and base-change proof paragraphs
(blueprint: sk-thm-sf-comp-composition).

The witnesses expose the actual natural isomorphisms; the refinement equation pins the
compactification comparisons to those of `localizingCompactificationCoherence`. The composition
normalization uses the unique interchange map whose open restriction is the identity.
The open base-change inverse is the specified open-adjunction transpose; the exchange
normalization is proper exchange followed by its open comparison and compactification
comparison. The final equation is pasting two successive Cartesian base changes.
The preservation and compactification-coherence interface is the existing proved
`AlgebraicGeometry.ProEtale.CondensedRing.localizingCompactificationCoherence`.

Proof, following the seven DAG steps:
1. Choose compactifications $f=pj$ and $g=qi$ using Nagata; all targets are qcqs in the standing
   setting. Apply Nagata to $ip:\overline X\to\overline Y$ and replace its model by a common
   dense refinement (the one-element case) to obtain $ip=rj'$, with $j'$ open and dense and $r$
   proper. The interchange lemma (1)-(2) gives $r^{-1}(Y)=\overline X$ and the unique natural
   map $$\iota_M:i_!Rp_*M\longrightarrow Rr_*j'_!M$$ whose restriction to $Y$ is the identity of
   $Rp_*M$. Indeed the canonical open restriction identifies $i^*Rr_*j'_!M$ with $Rp_*M$, and
   $\iota_M$ is its inverse's open-adjunction transpose. All opens here are quasi-compact; the
   proper/open square is Cartesian. The composite $(j'j,qr)$ is a compactification of $gf$.
2. For $M\in D^b_{\mathrm{ctf}}(\overline X,\Lambda)$, restriction of $\iota_M$ to $Y$ is the
   identity. On the closed complement $C=\overline Y\setminus Y$, its source is zero. Proper
   base change for $r$ identifies restriction of its target with the proper direct image of the
   restriction of $j'_!M$ to $W\setminus\overline X$, which is zero. The proper base-change
   theorem applies since $j'_!M$ is constructible of finite Tor amplitude by the open-image
   theorem. Thus the cone has zero open and closed restrictions and is zero by the open-closed
   exact sequence. Here the internal/section-module equivalence transports that exact sequence
   and its operations; exactness of the restrictions lets one apply it to cohomology in every
   degree. Both $i_!Rp_*$ and $Rr_*j'_!$ are exact and preserve sums on
   $\Loc(D^b_{\mathrm{ctf}})$ by the proper/open-image theorem. The map is a transformation of
   exact functors because it is constructed from derived adjunctions. The determination lemma
   therefore makes $\iota_M$ invertible for every $M$ in this localizing closure.
3. For $K\in\Loc(D^b_{\mathrm{ctf}}(X,\Lambda))$, open-image preservation puts $j_!K$ in the
   corresponding closure on $\overline X$. Apply $Rq_*$ to $\iota_{j_!K}$ and then the canonical
   direct-image and open compositors to obtain
   $$Rq_*i_!Rp_*j_!K\xrightarrow{\sim}Rq_*Rr_*j'_!j_!K\xrightarrow{\sim}R(qr)_*(j'j)_!K.$$ These
   are natural isomorphisms, and the final term computes $R(gf)_!K$ on the compactification of
   Step 1. Use compactification coherence to compare these model functors with the chosen
   $Rf_!$, $Rg_!$, and $R(gf)_!$. This defines $\alpha_{g,f}$. Both ends take
   $D^b_{\mathrm{ctf}}$ into $D^b_{\mathrm{ctf}}$ by compactification coherence, so the
   isomorphism restricts to that full subcategory.
4. Here are the mixed comparison laws needed for refinement and associativity, at the fixed
   admissible condensed coefficient. For a Cartesian proper/open square, let $\lambda_Q$ be
   derived open restriction followed by the inverse open unit and let $\Gamma_Q$ be the open-
   adjunction transpose of $\lambda_Q^{-1}$. These are the comparisons of Step 1: [lem-sfb-
   derived-open-restriction-normalization] fixes the restriction map. [lem-sfb-derived-open-
   restriction-mixed] and [lem-sfb-derived-open-restriction-successive] give its compatibility
   with composing proper maps and composing opens, respectively. Transpose these two equations,
   using [lem-weil-pbc-mate-pasting](1)-(2). They give
   $\Gamma_{Q_2Q_1}=(Rr_{2*}\Gamma_{Q_1})\circ(\Gamma_{Q_2}Rp_{1*})$ in the vertical case and
   $\Gamma_{Q_2Q_1}=(\Gamma_{Q_2}j_{1!})\circ(i_{2!}\Gamma_{Q_1})$ in the horizontal case, with
   the canonical compositors inserted. The identity clause of mate pasting gives the identity
   comparisons. Every square used here is Cartesian: this is $r^{-1}(Y)=\overline X$ for an
   interchange, and the boundary-preserving condition for a refinement. Thus no non-Cartesian or
   coefficient-specific pasting theorem is being applied.
5. Compare all compactification choices through common dense refinements and the canonical cocycle
   $\phi$. A refinement comparison before its final proper pushforward is the normalized
   Cartesian mixed map $\Gamma$ with source-side proper map the identity: both are adjoint to
   the same inverse restriction. Thus moving a refinement across an interchange is precisely a
   vertical or horizontal pasting identity for $\Gamma$ from Step 4. These identities prove that
   the model arrow in Step 3 commutes with every refinement. The cocycle cancels the
   intermediate comparisons, proving independence of choices, including nondense original
   models. For three composable maps, expand the two bracketings into a word of proper images
   and open extensions on common refined models. Disjoint interchanges commute by functoriality;
   overlapping proper/proper/open and proper/open/open moves are the two pasting equations of
   Step 4. Pure proper moves agree by associativity of the derived direct-image compositor, and
   pure open moves by the canonical composite open adjunctions [lem-sf-exact-localization-open-
   compositor]. Hence the bracketings agree as natural transformations before restriction to the
   localizing subcategory. Transport by the cocycle gives associativity on the chosen models.
   The identity compactification and the identity clauses of these comparisons give both unit
   laws. This argument uses equality of specified adjunction maps, rather than detection of
   equality on generators.
6. For the morphism $v$ of the standing setting, pull back $(j,p)$ to the compactification
   $(j_v,p_v)$ of $f'$, with projection $v':\overline X'\to\overline X$. Its open part need not
   be dense. The normalized open comparison is the inverse of the $j_{v!}\dashv j_v^*$ transpose
   of $$u^*K\simeq j_v^*v'^*j_!K.$$ [lem-sp-condensed-open-base-change-arbitrary] states its
   invertibility with exactly this adjunction normalization, for every commutative condensed
   coefficient ring. This is the blueprint's open/closed proof: it restricts to the identity on
   $X'$, and both sides vanish on the closed complement; the qc open-closed sequence detects its
   cone. For $K\in\Loc(D^b_{\mathrm{ctf}}(X,\Lambda))$, open-image preservation permits proper
   base change for $p$ at $j_!K$. It gives
   $$v^*Rp_*j_!K\xrightarrow{\sim}Rp_{v*}v'^*j_!K\xrightarrow{\sim}Rp_{v*}j_{v!}u^*K.$$ The
   second arrow is proper pushforward of the normalized open comparison. Compare the pulled-back
   compactification with the chosen one by compactification coherence. This constructs the
   stated base-change map in the asserted order. The base-change lemma (2)-(3) gives its
   localizing typing and independence of compactification comparisons; compactification
   coherence supplies preservation of $D^b_{\mathrm{ctf}}$ for the compact-support functors, and
   pullback preserves the constructible finite-Tor subcategories by the pullback lemma (applied
   only to the standing morphisms $u,v$), so it restricts there.
7. Take two composable Cartesian squares and use the literal successive base changes of the
   compactification. Expand the two compact-support exchange maps into proper exchange followed
   by the open exchange. The normalized open exchanges satisfy Cartesian pasting: by [lem-sp-
   condensed-open-base-change-arbitrary] their inverses are the open-adjunction transposes of
   the pullback-square comparison applied to the open unit. Pasting along the pullback functors,
   [lem-weil-pbc-mate-pasting](1), identifies both composites with that same transpose for the
   outer square. Proper exchanges satisfy the mate-pasting equation: each is unit, pullback-
   square comparison, counit, and the counit of a composite adjunction is the composite of the
   two counits. Substitute these two identities into the expanded composite. Naturality permits
   the open comparison to pass the intervening proper image, leaving exactly the proper exchange
   followed by the open exchange for the composite square, with canonical associators. The
   refinement/base-change equation commutes these composites with source refinement maps and
   their base changes (which need not be dense). Passing to common dense refinements on the new
   side and applying the compactification cocycle therefore carries the equality to all chosen
   compactifications. This proves the asserted compatibility with composing Cartesian squares,
   also after restriction to the full $D^b_{\mathrm{ctf}}$ subcategories.
-/
theorem sk_thm_sf_comp_composition
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
  ∃ (preserves : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    (∀ K, localizingClosureProEtale Λ X.obj.left K →
      localizingClosureProEtale Λ Y.obj.left
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ X.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ Y.obj.left
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K))),
  ∃ (comparison : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : Compactification f.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ d),
  ∃ (comp : ∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left)),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙
          rightDerivedLowerShriekOfCompactification Λ d) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ e),
  ∃ (openIso : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    D((c.i)_!open⟦Λ⟧) ⋙ moduleObjectDerivedPullback Λ (pullback.fst c.g v.hom.left) ≅
      moduleObjectDerivedPullback Λ a.hom.left ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧)),
  ∃ (pullback_preserves : ∀ (X Y : SepFinType k) (v : X ⟶ Y),
    (∀ K, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left ((moduleObjectDerivedPullback Λ v.hom.left).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ Y.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ X.obj.left
          ((moduleObjectDerivedPullback Λ v.hom.left).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((moduleObjectDerivedPullback Λ v.hom.left).obj K))),
  ∃ (exchange : ∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (_sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left),
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v.hom.left) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a.hom.left ⋙ rightDerivedLowerShriekOfCompactification Λ d)),
  -- refinement
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d : Compactification f.hom.left)
      (r : Compactification.DenseBoundaryCompactification f.hom.left)
      [QuasiCompact f.hom.left]
      (hc : r.obj ⟶ detSfBoundaryCompactification c)
      (hd : r.obj ⟶ detSfBoundaryCompactification d)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comparison f c d).hom.app K ≫ compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj) ∧
  -- comparison_id
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    comparison f c c = Iso.refl _) ∧
  -- comparison_cocycle
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d e : Compactification f.hom.left),
    comparison f c d ≪≫ comparison f d e = comparison f c e) ∧
  -- comp_normalized
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (T : Compactification.Triangle f.hom.left g.hom.left)
      (hT : IsSchemeTheoreticallyDominant T.q)
      [QuasiCompact (T.cf.g ≫ T.cg.i)]
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      (comp f g T.cf T.cg T.cfg).hom.app K =
        R((T.cg.g)_*⟦Λ⟧).map
          (m ≫ R((T.p)_*⟦Λ⟧).map
            ((openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj)) ∧
  -- comp_independent
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c c' : Compactification f.hom.left) (d d' : Compactification g.hom.left)
      (e e' : Compactification (f.hom.left ≫ g.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp f g c d e).hom.app K ≫ (comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map ((comparison f c c').hom.app K) ≫
        (comparison g d d').hom.app
          ⟨_, (preserves f c').1 K.obj K.property⟩ ≫ (comp f g c' d' e').hom.app K) ∧
  -- unit_left
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp (𝟙 X) f (Compactification.ofIsProper (𝟙 X.obj.left)) c
      (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map ((identity Λ X.obj.left).hom.app K.obj)) ∧
  -- unit_right
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp f (𝟙 Y) c (Compactification.ofIsProper (𝟙 Y.obj.left))
      (c.copy (Category.comp_id f.hom.left))).hom.app K =
      (identity Λ Y.obj.left).hom.app ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
  -- assoc
  (∀ {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification h.hom.left)
      (cd : Compactification (f.hom.left ≫ g.hom.left))
      (de : Compactification (g.hom.left ≫ h.hom.left))
      (cde : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (rightDerivedLowerShriekOfCompactification Λ e).map ((comp f g c d cd).hom.app K) ≫
        (comp (f ≫ g) h cd e cde).hom.app K =
      (comp g h d e de).hom.app ⟨_, (preserves f c).1 K.obj K.property⟩ ≫
        (comp f (g ≫ h) c de (cde.copy (Category.assoc _ _ _).symm)).hom.app K) ∧
  -- open_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left),
    (openIso (a := a) (v := v) sq c).inv = openExchange Λ sq c) ∧
  -- exchange_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (exchange (a := a) (v := v) sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map ((openIso (a := a) (v := v) sq c).hom.app K.obj) ≫
        (comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- exchange_independent
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X' ⟶ X} {v : Y' ⟶ Y}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v.hom.left).map ((comparison f c c').hom.app K) ≫
        (exchange (a := a) (v := v) sq c' d').hom.app K =
      (exchange (a := a) (v := v) sq c d).hom.app K ≫ (comparison f' d d').hom.app
        ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- Pasting in the base-change direction, with the canonical pullback compositors.
  (∀ {X Y X' Y' X'' Y'' : SepFinType k}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      {a : X' ⟶ X} {v : Y' ⟶ Y} {b : X'' ⟶ X'} {w : Y'' ⟶ Y'}
      (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
      (sq' : IsPullback b.hom.left f''.hom.left f'.hom.left w.hom.left)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (e : Compactification f''.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (leftDerivedUpperStarComp Λ w.hom.left v.hom.left).hom.app
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj) ≫
      (moduleObjectDerivedPullback Λ w.hom.left).map
        ((exchange (a := a) (v := v) sq c d).hom.app K) ≫
      (exchange (a := b) (v := w) sq' d e).hom.app
        ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩ =
    (exchange (a := b ≫ a) (v := w ≫ v) (sq'.paste_horiz sq) c e).hom.app K ≫
      (rightDerivedLowerShriekOfCompactification Λ e).map
        ((leftDerivedUpperStarComp Λ b.hom.left a.hom.left).hom.app K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
