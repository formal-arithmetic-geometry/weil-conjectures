/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.CategoryTheory.ModulePullbackTensorIso

/-! # Quasi-coherent algebra direct image on algebraic stacks

Source: Stacks Project, stacks-cohomology.tex, Tags 077A, 0GQQ, 0GQR and 0GQF
(blueprint: lem-sfb-stack-qcqs-algebra-direct-image).

The comma category of arrows f(x) → y is the usual model of the 2-base change
by the scheme test y: an arrow factors uniquely into its vertical isomorphism and
its cartesian arrow over the map to the test scheme. Its compatible section ring
is therefore Γ(X ×_Y T,A). The comparison below is fixed by the adjunction counit,
not an arbitrary ring isomorphism. All coefficient carriers lie in a common
ambient universe, retaining separate scheme, object and morphism universes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Quasi-coherent commutative algebras, using the existing ringed-site predicate.
Source: Stacks 077A, multiplicative form (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
abbrev ModuliQCAlg {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (hX : IsFibredInGroupoids X) :=
  ObjectProperty.FullSubcategory
    (fun A : ModuliAlgebraSheaf X hX ↦ IsQuasicoherentModuliAlgebra A)

/-- A smooth scheme object, without requiring the scheme map to be surjective.
The vertical isomorphism identifies the represented test with the given object.
Source: Stacks 0GQQ, smooth tests (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
def IsSmoothModuliObject {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    : ObjectProperty X.obj := fun x ↦
  ∃ t : BasedFunctor (discreteModuli (yoneda.obj (X.p.obj x))) X,
    ModuliSpaceTest @Smooth t ∧
      ∃ e : t.obj (CostructuredArrow.mk (𝟙 (yoneda.obj (X.p.obj x)))) ≅ x,
        X.p.IsHomLift (𝟙 (X.p.obj x)) e.hom

/-- Objects of the smooth-etale site: smooth scheme tests and all their arrows.
Source: Stacks 0GQF, 0GQQ (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
abbrev ModuliSmoothSite {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S)) :=
  (IsSmoothModuliObject X).FullSubcategory

/-- Etale coverings on smooth scheme tests, via their actual underlying scheme maps.
Source: Stacks 0GQF (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
def moduliSmoothEtaleTopology {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S)) :=
  (Scheme.etalePrecoverage.comap
    ((IsSmoothModuliObject X).ι ⋙ moduliSchemeForget X)).toGrothendieck

/-- The ring-presheaf functor forgetting only the structure morphism and quasi-coherence.
Source: Stacks 077A (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
def moduliQCAlgPresheaf {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (hX : IsFibredInGroupoids X) :
    ModuliQCAlg X hX ⥤ (X.objᵒᵖ ⥤ CommRingCat.{max (u + 1) v w}) where
  obj A := A.obj.right.obj
  map a := a.hom.right.hom

/-- Restrict the existing algebra sheaf to smooth tests, with unchanged ring maps.
Source: Stacks 0GQF (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
def moduliSmoothAlgebraPresheaf {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (hX : IsFibredInGroupoids X) (A : ModuliQCAlg X hX) :=
  (IsSmoothModuliObject X).ι.op ⋙ A.obj.right.obj

/-- Tensor pullback on quasi-coherent algebras, in its section-normalized
precomposition form. The structure equation fixes the O-algebra structure too.
Extension of scalars along the identity regular-function comparison is precisely
this precomposition: r tensor a maps to r a.
Source: Stacks 077A and 06WH (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
structure ModuliAlgebraPullback {S : Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y) where
  /-- The functor on the actual quasi-coherent algebra categories. -/
  functor : ModuliQCAlg Y hY ⥤ ModuliQCAlg X hX
  /-- Sectionwise precomposition, natural in algebras and test arrows. -/
  sections : functor ⋙ moduliQCAlgPresheaf X hX ≅
    moduliQCAlgPresheaf Y hY ⋙
      (Functor.whiskeringLeft X.objᵒᵖ Y.objᵒᵖ CommRingCat).obj f.toFunctor.op
  /-- The comparison preserves the specified regular-function structure map. -/
  structure_map (A : ModuliQCAlg Y hY) (x : X.obj)
      (r : (moduliStructurePresheaf X).obj (op x)) :
    (sections.hom.app A).app (op x) (((functor.obj A).obj.hom.hom.app (op x)) r) =
      A.obj.hom.hom.app (op (f.obj x))
        (ULift.up (Eq.mp (congrArg
          (fun T : Over S ↦ (Scheme.Γ.obj (op T.left) : Type u)) (f.w_obj x).symm) r.down))

/-- Compatible section rings on the comma model of the actual scheme 2-base change.
Source: Stacks 0GQQ, 06W6 (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
def moduliAlgebraImageSections {S : Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (f : BasedFunctor X Y) (A : ModuliQCAlg X hX) (y : Y.obj) :=
  RingCat.sectionsSubring
    ((CostructuredArrow.proj f.toFunctor y).op ⋙ A.obj.right.obj ⋙
      forget₂ CommRingCat RingCat)

/-- The identity object of the represented scheme test.
Source: Stacks 06W6 (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
abbrev moduliSchemeTestTerminal {S : Scheme.{u}} (T : Over S) :
    (discreteModuli (yoneda.obj T)).obj :=
  CostructuredArrow.mk (𝟙 (yoneda.obj T))

/-- The canonical arrow from a scheme over T to its terminal test.
Source: Stacks 06W6 (blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
def moduliSchemeTestToTerminal {S : Scheme.{u}} (T : Over S)
    (z : (discreteModuli (yoneda.obj T)).obj) : z ⟶ moduliSchemeTestTerminal T :=
  CostructuredArrow.homMk (yoneda.preimage z.hom) (by simp)

/-- The right adjoint and its canonical smooth-chart algebra comparison.
Source: Stacks 077A, 0GQQ, 0GQR
(blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
structure ModuliAlgebraDirectImage {S : Scheme.{u}}
    {X Y : BasedCategory.{v, w} (Over S)} (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (f : BasedFunctor X Y)
    (P : ModuliAlgebraPullback hX hY f) where
  /-- Direct image takes values in quasi-coherent commutative algebras. -/
  functor : ModuliQCAlg X hX ⥤ ModuliQCAlg Y hY
  /-- The algebra adjunction. -/
  adjunction : P.functor ⊣ functor
  /-- Algebra identification on every smooth scheme test. -/
  sections (A : ModuliQCAlg X hX) (y : Y.obj) (hy : IsSmoothModuliObject Y y) :
    (functor.obj A).obj.right.obj.obj (op y) ≃+* moduliAlgebraImageSections hX f A y
  /-- The identification is the restriction/counit comparison, on every component. -/
  sections_counit (A : ModuliQCAlg X hX) (y : Y.obj)
      (hy : IsSmoothModuliObject Y y) (s : (functor.obj A).obj.right.obj.obj (op y))
      (i : CostructuredArrow f.toFunctor y) :
    (sections A y hy s).val (op i) =
      (adjunction.counit.app A).hom.right.hom.app (op i.left)
        ((P.sections.inv.app (functor.obj A)).app (op i.left)
          ((functor.obj A).obj.right.obj.map i.hom.op s))
  /-- The displayed section ring on the recorded 2-fibre product itself.
  The restriction diagram retains the original section rings and algebra operations. -/
  baseChange_sections (A : ModuliQCAlg X hX) (T : Over S)
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y)
      (ht : ModuliSpaceTest @Smooth t) :
    (functor.obj A).obj.right.obj.obj (op (t.obj (moduliSchemeTestTerminal T))) ≃+*
      RingCat.sectionsSubring
        ((moduliTwoFiberFst f t).toFunctor.op ⋙ A.obj.right.obj ⋙
          forget₂ CommRingCat RingCat)
  /-- Its component at (x,w,α) is restriction to α followed by the counit.
  This also fixes the comparison naturally in algebras and scheme-test arrows. -/
  baseChange_counit (A : ModuliQCAlg X hX) (T : Over S)
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y)
      (ht : ModuliSpaceTest @Smooth t)
      (s : (functor.obj A).obj.right.obj.obj (op (t.obj (moduliSchemeTestTerminal T))))
      (i : (moduliTwoFiberProduct f t).obj) :
    (baseChange_sections A T t ht s).val (op i) =
      (adjunction.counit.app A).hom.right.hom.app (op i.obj.left)
        ((P.sections.inv.app (functor.obj A)).app (op i.obj.left)
          ((functor.obj A).obj.right.obj.map
            (i.obj.hom ≫ t.map (moduliSchemeTestToTerminal T i.obj.right)).op s))
  /-- Compatibility with algebra homomorphisms, on all base-change components. -/
  sections_naturality {A B : ModuliQCAlg X hX} (a : A ⟶ B) (y : Y.obj)
      (hy : IsSmoothModuliObject Y y) (s : (functor.obj A).obj.right.obj.obj (op y))
      (i : CostructuredArrow f.toFunctor y) :
    (sections B y hy ((functor.map a).hom.right.hom.app (op y) s)).val (op i) =
      a.hom.right.hom.app (op i.left) ((sections A y hy s).val (op i))
  /-- Compatibility with every arrow between smooth tests. -/
  sections_restriction (A : ModuliQCAlg X hX) {y z : Y.obj} (b : y ⟶ z)
      (hy : IsSmoothModuliObject Y y) (hz : IsSmoothModuliObject Y z)
      (s : (functor.obj A).obj.right.obj.obj (op z))
      (i : CostructuredArrow f.toFunctor y) :
    (sections A y hy ((functor.obj A).obj.right.obj.map b.op s)).val (op i) =
      (sections A z hz s).val (op ((CostructuredArrow.map b).obj i))

/-- The canonical compositor is characterized by the pasted counit, using the
section-normalized identification of composite pullback with iterated pullback.
Source: Stacks 077A, uniqueness of right adjoints
(blueprint: lem-sfb-stack-qcqs-algebra-direct-image). -/
structure ModuliAlgebraDirectImageComposition {S : Scheme.{u}}
    {X Y Z : BasedCategory.{v, w} (Over S)}
    {hX : IsFibredInGroupoids X} {hY : IsFibredInGroupoids Y}
    {hZ : IsFibredInGroupoids Z} {f : BasedFunctor X Y} {g : BasedFunctor Y Z}
    (Pf : ModuliAlgebraPullback hX hY f) (Pg : ModuliAlgebraPullback hY hZ g)
    (Pgf : ModuliAlgebraPullback hX hZ (f.comp g))
    (Rf : ModuliAlgebraDirectImage hX hY f Pf)
    (Rg : ModuliAlgebraDirectImage hY hZ g Pg)
    (Rgf : ModuliAlgebraDirectImage hX hZ (f.comp g) Pgf) where
  /-- Canonical associativity of tensor pullback. -/
  pullback : Pgf.functor ≅ Pg.functor ⋙ Pf.functor
  /-- The pullback comparison is the identity in precomposition coordinates. -/
  pullback_sections (A : ModuliQCAlg Z hZ) (x : X.obj)
      (s : (Pgf.functor.obj A).obj.right.obj.obj (op x)) :
    (Pf.sections.hom.app (Pg.functor.obj A)).app (op x)
      (((pullback.hom.app A).hom.right.hom.app (op x)) s) =
        (Pg.sections.inv.app A).app (op (f.obj x))
          ((Pgf.sections.hom.app A).app (op x) s)
  /-- A natural algebra isomorphism, hence compatibility with all algebra maps. -/
  iso : Rf.functor ⋙ Rg.functor ≅ Rgf.functor
  /-- The compositor is fixed by the two adjunction counits. -/
  counit (A : ModuliQCAlg X hX) :
    Pgf.functor.map (iso.hom.app A) ≫ Rgf.adjunction.counit.app A =
      pullback.hom.app (Rg.functor.obj (Rf.functor.obj A)) ≫
        Pf.functor.map (Rg.adjunction.counit.app (Rf.functor.obj A)) ≫
          Rf.adjunction.counit.app A

/-- Algebra adjunction, smooth-chart direct image, canonical composition, and
comparison of fppf and smooth-etale sheaf surjections.

Source: Stacks Project, stacks-cohomology.tex, Tags 077A, 0GQQ, 0GQR and 0GQF
(blueprint: lem-sfb-stack-qcqs-algebra-direct-image).

Proof:
1. Use lem-sfb-stack-qcqs-module-adjunction. Transpose multiplication composed
with the two counits, and transpose the unit, using
lem-weil-pbc-ringed-topoi-module-pullback-tensor and
lem-sfb-stack-quasi-coherent-scheme-restriction. Tensor powers remain
quasi-coherent by lem-sfb-stack-qcoh-flat-atlas-exactness.
2. Injectivity of the module adjunction checks associativity, commutativity and
both unit laws after transposition. Counit naturality checks that algebra maps
are preserved. These constructions yield a functor of commutative algebras.
3. A module map preserves multiplication and unit if and only if its transpose
does. Restrict the natural module Hom bijections to algebra maps, obtaining
the required adjunction with section-normalized tensor pullback.
4. Smooth tests are flat by lem-pc-smooth-flat. Apply
lem-sfb-stack-flat-module-pushforward-comparison to the underlying module.
Its tensor and unit normalizations make this the displayed algebra comparison.
The comma/base-change equivalence retains all arrows and original section rings;
lem-sfb-algebraic-stack-fibre-products ensures these are algebraic fibre stacks.
Naturality gives restriction on the smooth-etale site and compatibility with maps.
5. By lem-sfb-stack-qcqs-composition-affine the composite is qcqs. Pullback is
precomposition, hence its compositor is fixed on sections. Apply
lem-cat-right-adjoint-composition to the two algebra adjunctions. Uniqueness of
right adjoints gives the natural algebra isomorphism with the pasted counit.
6. Forget multiplication. By lem-sfb-stack-qcoh-flat-atlas-exactness, the ambient
fppf cokernel is the quasi-coherent cokernel, and epimorphisms restrict to
surjections on every flat test's small etale site. Smooth tests are flat. Conversely
choose the smooth surjective atlas in def-sfb-algebraic-moduli-stack; etale-local
lifting there forces the quasi-coherent cokernel, hence the fppf cokernel, to vanish.
Forgetting multiplication changes none of the lifting conditions. -/
theorem exists_moduliAlgebraDirectImage {k : Type u} [Field k]
    (X Y : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (f : BasedFunctor X Y) (hfqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, v, w, v, w} f)
    (hfqs : IsQuasiSeparatedAlgebraicModuliMap f) :
    (∃ (P : ModuliAlgebraPullback hX.1.1 hY.1.1 f)
      (R : ModuliAlgebraDirectImage hX.1.1 hY.1.1 f P),
      ∀ (Z : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
        (hZ : IsAlgebraicModuliStack Z) (g : BasedFunctor Y Z),
        IsQuasiCompactAlgebraicModuliMap.{u, v, w, v, w, v, w} g →
        IsQuasiSeparatedAlgebraicModuliMap g →
        ∃ (Pg : ModuliAlgebraPullback hY.1.1 hZ.1.1 g)
          (Pgf : ModuliAlgebraPullback hX.1.1 hZ.1.1 (f.comp g))
          (Rg : ModuliAlgebraDirectImage hY.1.1 hZ.1.1 g Pg)
          (Rgf : ModuliAlgebraDirectImage hX.1.1 hZ.1.1 (f.comp g) Pgf),
          Nonempty (ModuliAlgebraDirectImageComposition P Pg Pgf R Rg Rgf)) ∧
    ∀ (W : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
      (hW : IsAlgebraicModuliStack W),
      (∀ A : ModuliQCAlg W hW.1.1,
        Presheaf.IsSheaf (moduliSmoothEtaleTopology W)
          (moduliSmoothAlgebraPresheaf W hW.1.1 A)) ∧
      ∀ (A B : ModuliQCAlg W hW.1.1) (a : A ⟶ B),
        (IsSurjectiveModuliAlgebra a.hom ↔
          Presheaf.IsLocallySurjective (moduliSmoothEtaleTopology W)
            (Functor.whiskerLeft (IsSmoothModuliObject W).ι.op a.hom.right.hom)) ∧
        (IsSurjectiveModuliAlgebra a.hom ↔
          ∀ (x : W.obj), IsSmoothModuliObject W x →
            ∀ s : B.obj.right.obj.obj (op x),
              Presheaf.imageSieve a.hom.right.hom s ∈
                (Scheme.etalePrecoverage.comap (moduliSchemeForget W)).toGrothendieck x) := by
  sorry

end CategoryTheory
