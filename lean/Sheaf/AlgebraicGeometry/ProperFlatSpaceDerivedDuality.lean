module

public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.AlgebraicGeometry.AffineAdjointUnitProperties
import Sheaf.AlgebraicGeometry.AffineEtaleHypercoverRefinement
import Sheaf.AlgebraicGeometry.SpaceNegativeExtHyperdescent
import Sheaf.AlgebraicGeometry.SpaceRelativePerfectBaseChange
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization

/-! # Proper flat algebraic-space derived duality

Source: Stacks Project, spaces-duality.tex, Tags 0E5X, 0E5Z, 0E61, 0E6C and 0E6E;
spaces-more-morphisms.tex, Tag 0DKN
(blueprint: lem-sfb-proper-flat-space-derived-duality).

Finite presentation is local finite presentation together with the quasi-compactness
and quasi-separatedness already implied by properness. No global dimension or
cohomological bound is imposed; boundedness is local on the small étale site.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w wZ

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]

/-- Existence, local finiteness, rigidity, and arbitrary scheme base change of the
relative dualizing trace pair. The affine Hom map is part of
`IsRelativeDualizingTracePair`, and is composition with the pulled trace followed by
RΓ and its fixed affine structure-sheaf comparison.
Source: Stacks, Tags 0E5X, 0E5Z, 0E61 and 0E6C; Tag 0DKN
(blueprint: lem-sfb-proper-flat-space-derived-duality).

Proof:
1. Over an affine test V, properness makes X_V qcqs. Take the right adjoint a_V
   of Rf_V,* and its counit, and put W_V = a_V(O_V). Adjunction gives the Hom
   bijection by composition with that counit. Affine étale derived module realization
   identifies its target with Hom in D(A), taking O_V to A[0]. The affine adjoint-unit
   properties make W_V relatively perfect, Rf_V,*W_V connective, and its derived
   endomorphism object O. Thus its negative self Ext groups vanish.
2. Affine proper-flat adjoint base change identifies pullbacks of W_V with the
   corresponding W_V', preserving counits. Yoneda uniqueness of representing pairs
   gives uniqueness of these identifications and their identity and cocycle laws.
3. Choose an affine-component étale hypercover of the base and pull it to X. The
   W_V and these transition isomorphisms form a cartesian derived system with zero
   negative self Exts. Negative-Ext hyperdescent glues it to K in D_QCoh. Relative
   perfectness descends étale locally. It implies pseudo-coherence and, by testing
   its relative Tor bound on the inverse-image structure module itself, local bounds
   for the cohomology of K. These bounds may vary on the covering.
4. Let C = Rf_*K. Base change identifies its restrictions with the connective
   Rf_V,*W_V, so C is connective. Negative Hom from C to O vanishes by t-structure
   orthogonality. The compatible affine traces therefore glue uniquely by morphism
   hyperdescent on the base, producing the actual trace C to O.
5. Refine the chosen hypercover over any affine test V. Both its pullback of K and
   W_V restrict to the same affine representing objects. Negative cross Exts vanish,
   so morphism descent glues their trace-compatible local isomorphisms and inverses.
   Injectivity of descent on the base identifies their traces. This proves the Hom
   characterization on every affine test. The same argument glues the unique local
   representing isomorphisms between any two global trace pairs, proving rigidity.
6. For an arbitrary scheme base change, flat proper derived exchange is invertible.
   Compose its inverse with the pulled trace and the canonical structure pullback.
   Relative perfectness survives base change, and transitivity of pullback and
   exchange makes every further affine test the test for the original composite.
   It is therefore a relative dualizing pair. Rigidity gives the unique displayed
   trace-compatible isomorphism to every other pair on that base change. -/
theorem properFlatSpaceDerivedDuality (Y : Over S) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace Y) (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f) :
    ∃ P : RelativeDualizingTracePair Y f,
      IsRelativeDualizingTracePair P ∧ IsPseudoCoherent X P.complex ∧
      (∀ V : X.SmallEtaleModel, ∃ R : Sieve V, R ∈ X.smallEtaleModelTopology V ∧
        ∀ (U : X.SmallEtaleModel) (i : U ⟶ V), R i → ∃ a b : ℤ,
          ∀ n : ℤ, n < a ∨ b < n →
            IsZero ((SheafOfModules.overFunctor X.smallStructureRings U).obj
              ((DerivedCategory.homologyFunctor X.SmallModules n).obj P.complex))) ∧
      (∀ Q : RelativeDualizingTracePair Y f, IsRelativeDualizingTracePair Q →
        ∃! e : P.complex ≅ Q.complex, TracePreserving P Q e) ∧
      (∀ (Y' : Over S) (g : Y' ⟶ Y) (X' : AlgebraicSpace S)
        (p : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
        (sq : IsPullback p f' f (traceSchemeMap g)),
        (∃ t : (derivedDirectImage f').obj ((spaceDerivedPullback p).obj P.complex) ⟶
            (schemeSpace Y').derivedStructure,
          IsRelativeDualizingTracePair
            (RelativeDualizingTracePair.mk ((spaceDerivedPullback p).obj P.complex) t) ∧
          TraceBaseChangeCompatible P ⟨(spaceDerivedPullback p).obj P.complex, t⟩
            g p sq.w (Iso.refl _)) ∧
        ∀ Q : RelativeDualizingTracePair Y' f', IsRelativeDualizingTracePair Q →
          ∃! e : (spaceDerivedPullback p).obj P.complex ≅ Q.complex,
            TraceBaseChangeCompatible P Q g p sq.w e) := by
  sorry

/-- The identity base-change comparison is the canonical derived pullback identity,
and it preserves the trace.
Source: Stacks, Tags 0E5Z and 0E6C
(blueprint: lem-sfb-proper-flat-space-derived-duality).
Proof: exchange and structure pullback for the identity are their ordinary unit
comparisons after deriving. Hence the identity pullback comparison preserves trace.
The affine Hom characterization and Yoneda rigidity give uniqueness. -/
theorem properFlatSpaceDerivedDuality_id (Y : Over S) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace Y) (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f) (P : RelativeDualizingTracePair Y f)
    (hP : IsRelativeDualizingTracePair P) :
    ∃! e : (spaceDerivedPullback (𝟙 X)).obj P.complex ≅ P.complex,
      TraceBaseChangeCompatible P P (𝟙 Y) (𝟙 X) (by
        have hi : traceSchemeMap (𝟙 Y) = 𝟙 (schemeSpace Y) := by
          ext : 2
          exact yoneda.map_id Y
        rw [hi]
        simp) e ∧
        e = (spaceDerivedPullbackId X).app P.complex := by
  sorry

/-- Direct and iterated base-change isomorphisms agree after the canonical pullback
composition comparison. All three isomorphisms are characterized by trace preservation.
Source: Stacks, Tags 0E5Z and 0E6C
(blueprint: lem-sfb-proper-flat-space-derived-duality).
Proof: composition of the canonical exchange maps agrees with the exchange for the
pasted square. Structure pullback also composes. Thus the iterated isomorphism
preserves the same pulled trace as the direct one; uniqueness of a trace-preserving
representing isomorphism identifies them. -/
theorem properFlatSpaceDerivedDuality_comp
    (Y Y' Y'' : Over S) (g : Y' ⟶ Y) (k : Y'' ⟶ Y')
    (X X' X'' : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (f' : X' ⟶ schemeSpace Y') (f'' : X'' ⟶ schemeSpace Y'')
    (p : X' ⟶ X) (q : X'' ⟶ X')
    (sq₁ : IsPullback p f' f (traceSchemeMap g))
    (sq₂ : IsPullback q f'' f' (traceSchemeMap k))
    (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f)
    (P : RelativeDualizingTracePair Y f) (Q : RelativeDualizingTracePair Y' f')
    (R : RelativeDualizingTracePair Y'' f'')
    (hP : IsRelativeDualizingTracePair P) (hQ : IsRelativeDualizingTracePair Q)
    (hR : IsRelativeDualizingTracePair R)
    (e₁ : (spaceDerivedPullback p).obj P.complex ≅ Q.complex)
    (e₂ : (spaceDerivedPullback q).obj Q.complex ≅ R.complex)
    (e₀ : (spaceDerivedPullback (q ≫ p)).obj P.complex ≅ R.complex)
    (he₁ : TraceBaseChangeCompatible P Q g p sq₁.w e₁)
    (he₂ : TraceBaseChangeCompatible Q R k q sq₂.w e₂)
    (he₀ : TraceBaseChangeCompatible P R (k ≫ g) (q ≫ p) (by
      rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc]
      congr 1) e₀) :
    e₀ = (spaceDerivedPullbackComp p q).app P.complex ≪≫
      (spaceDerivedPullback q).mapIso e₁ ≪≫ e₂ := by
  sorry


section SchemeComparison

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- A presentation of the Zariski/étale comparison for one represented scheme morphism.
Both equivalences are pinned, on their underlying ambient functors, to the actual
right-derived restriction to Zariski opens. The two direct-image presentations are
identified with the existing K-injective direct images. Thus these are presentations
of the same operations, rather than arbitrary functors or coefficient maps.
Source: Stacks, Tags 071Q, 08GH and 0E6E
(blueprint: lem-sfb-proper-flat-space-derived-duality). -/
structure SchemeDualizingTraceComparison {U Y : Over S} (f : U ⟶ Y) where
  /-- The full-subcategory presentation of the canonical étale Rf_*. -/
  etalePushforward : QCohDirectImagePresentation (traceSchemeMap f)
  /-- The Zariski full-subcategory presentation. -/
  zariskiPushforward : schemeDerivedQCohCategory U.left ⥤ schemeDerivedQCohCategory Y.left
  /-- It is the canonical ambient Zariski Rf_*, on both objects and morphisms. -/
  zariskiPushforwardComparison : zariskiPushforward ⋙ (schemeDerivedQCohProperty Y.left).ι ≅
    (schemeDerivedQCohProperty U.left).ι ⋙
      RingedSpace.derivedModuleDirectImage f.left.toLRSHom.toShHom
  /-- The source Zariski/étale equivalence, directed as R epsilon_*. -/
  source : (schemeSpace U).DerivedQCoh ≌ schemeDerivedQCohCategory U.left
  /-- The target Zariski/étale equivalence, in the same direction. -/
  target : (schemeSpace Y).DerivedQCoh ≌ schemeDerivedQCohCategory Y.left
  /-- Its source functor really is derived restriction to all Zariski opens. -/
  sourceRestriction : source.functor ⋙ (schemeDerivedQCohProperty U.left).ι ≅
    (schemeSpace U).derivedQCohProperty.ι ⋙
      (smallSchemeRestriction (schemeSpace U) (affineIdentityChart U)).rightDerivedFunctor
  /-- Its target functor really is derived restriction to all Zariski opens. -/
  targetRestriction : target.functor ⋙ (schemeDerivedQCohProperty Y.left).ι ≅
    (schemeSpace Y).derivedQCohProperty.ι ⋙
      (smallSchemeRestriction (schemeSpace Y) (affineIdentityChart Y)).rightDerivedFunctor
  /-- The commuting derived pushforward square, on the full subcategories. -/
  pushforward : source.inverse ⋙ etalePushforward.functor ≅
    zariskiPushforward ⋙ target.inverse
  /-- The Zariski structure complex, with its quasi-coherence proof. -/
  structureObject : schemeDerivedQCohCategory Y.left
  /-- Its specified identification with O_Y[0]. -/
  structureObjectIso : structureObject.obj ≅
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings Y.left.toRingedSpace))
  /-- The corresponding étale structure-object identification. -/
  structureComparison : (target.inverse.obj structureObject).obj ≅
    (schemeSpace Y).derivedStructure

/-- Transport the actual Zariski adjunction counit across the comparison square.
The formula retains the counit, the full inclusions, and the structure identifications;
it does not replace the trace by an arbitrary morphism.
Source: Stacks, Tag 0E6E (blueprint: lem-sfb-proper-flat-space-derived-duality). -/
def schemeDualizingAdjunctionTrace {U Y : Over S} {f : U ⟶ Y}
    (C : SchemeDualizingTraceComparison f)
    (a : schemeDerivedQCohCategory Y.left ⥤ schemeDerivedQCohCategory U.left)
    (adj : C.zariskiPushforward ⊣ a) :
    (derivedDirectImage (traceSchemeMap f)).obj
        (C.source.inverse.obj (a.obj C.structureObject)).obj ⟶
      (schemeSpace Y).derivedStructure :=
  (C.etalePushforward.comparison.inv.app
      (C.source.inverse.obj (a.obj C.structureObject))) ≫
    (schemeSpace Y).derivedQCohProperty.ι.map
      (C.pushforward.hom.app (a.obj C.structureObject) ≫
        C.target.inverse.map (adj.counit.app C.structureObject)) ≫
    C.structureComparison.hom

/-- On schemes over an affine base the pair is f! O with its adjunction trace.
The comparison exists, and the conclusion holds for every presentation of it and
for every choice of the right adjoint, so it applies in particular to the canonical
Zariski/étale comparison and to any already chosen f!.
Source: Stacks, Tag 0E6E and the third remark after Tag 0E5X
(blueprint: lem-sfb-proper-flat-space-derived-duality).

Proof (step 7 of the node): the Zariski/étale equivalences on D_QCoh are given by
exact epsilon pullback and right-derived restriction. They carry structure modules
to each other and intertwine K-injective direct image, giving the displayed comparison
presentations. Over the affine base the affine representing object is a(O), with the
counit trace. Transport its adjunction through these equivalences and their direct-image
square. This yields a right adjoint to Zariski Rf_*. Every chosen Zariski right adjoint
is uniquely isomorphic to it, with its counit, by the adjunction Hom bijections.
Evaluation at O and transport back to the étale category give precisely the counit
formula schemeDualizingAdjunctionTrace. The original pair represents the same affine
Hom functor, so Yoneda gives its unique trace-preserving isomorphism to that object. -/
theorem properFlatSpaceDerivedDuality_schemeComparison
    (U Y : Over S) (f : U ⟶ Y) [IsAffine Y.left]
    (hproper : MapIsProper (traceSchemeMap f))
    (hflat : MapIsFlat (traceSchemeMap f))
    (hfp : MapIsLocallyOfFinitePresentation (traceSchemeMap f))
    (P : RelativeDualizingTracePair Y (traceSchemeMap f))
    (hP : IsRelativeDualizingTracePair P) :
    Nonempty (SchemeDualizingTraceComparison f) ∧
    ∀ C : SchemeDualizingTraceComparison f,
      C.zariskiPushforward.IsRightAdjoint ∧
      ∀ (a : schemeDerivedQCohCategory Y.left ⥤ schemeDerivedQCohCategory U.left)
        (adj : C.zariskiPushforward ⊣ a),
        ∃! e : P.complex ≅ (C.source.inverse.obj (a.obj C.structureObject)).obj,
          TracePreserving P
            ⟨(C.source.inverse.obj (a.obj C.structureObject)).obj,
              schemeDualizingAdjunctionTrace C a adj⟩ e := by
  sorry

end SchemeComparison

end AlgebraicGeometry.AlgebraicSpace
