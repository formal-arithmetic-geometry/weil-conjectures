/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarData
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.InternalActionSite.EquivariantModuleSheafificationReflector
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Internal condensed group algebras and the exact forgetful functor

Source: main-20261015, six-functors direct-image stability, paragraph (3),
agent-formulated internal bar input (independent reference WANTED).
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).

All normalization formulas use the actual free adjunction and internal relative tensor.
The data below specify constructions uniquely by their generators, without choosing
objects from the postponed existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction.InternalBar

namespace Profinite.CondensedAction.GroupAlgebra

variable (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The condensed group as its representable sheaf of continuous maps, lifted into
its coefficient universe. Source: paragraph (3), internal bar input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
abbrev groupSet : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) :=
  ((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj (Profinite.of G)

/-- The internal group algebra's underlying module is the existing free module.
Source: paragraph (3), internal bar input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
abbrev algebra : Modules A := (free A).obj (groupSet G)

/-- Generalized generators are the unit of the recorded free adjunction.
Source: paragraph (3), internal bar input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
def freeGenerator (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (S : Profinite.{u}) (x : X.obj.obj (op S)) :
    sectionModule A ((free A).obj X) S :=
  (((freeAdjunction A).unit.app X).hom.app (op S)) x

/-- The generator indexed by a continuous G-valued section.
Source: paragraph (3), internal bar input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
def groupGenerator (S : Profinite.{u}) (g : C(S, G)) : sectionModule A (algebra A G) S :=
  freeGenerator A (groupSet G) S (ULift.up (CompHausLike.ofHom _ g))

/-- Normalized group-algebra multiplication and module equivalence. The comparison
with forgetting pins every module action to the original sectionwise action.
Source: paragraph (3), internal group-algebra input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
structure AlgebraEquivalence where
  /-- No commutativity of this monoid is required. -/
  [monoid : MonObj (algebra A G)]
  /-- The product extends the group law on generalized generators. -/
  multiplication : ∀ (S : Profinite.{u}) (g h : C(S, G)),
    onSections A (MonObj.mul (X := algebra A G)) S
      (pureTensor A _ _ S (groupGenerator A G S g) (groupGenerator A G S h)) =
        groupGenerator A G S (g * h)
  /-- The algebra unit sends 1 to the generator of the group identity. -/
  unit : ∀ S : Profinite.{u},
    onSections A (MonObj.one (X := algebra A G)) S (regularOne A S) =
      groupGenerator A G S 1
  /-- The categories of natural group actions and internal algebra modules agree. -/
  equivalence : ActionModule A G ≌ Mod (Modules A) (algebra A G)
  /-- The equivalence commutes with forgetting to the original internal modules. -/
  underlying : equivalence.functor ⋙ Mod.forget (algebra A G) ≅ forgetAction
  /-- The forward action is uniquely normalized by [g] tensor m maps to gm. -/
  action : ∀ (M : ActionModule A G) (S : Profinite.{u}) (g : C(S, G))
      (m : sectionModule A (equivalence.functor.obj M).X S),
    onSections A (underlying.hom.app M) S
      (onSections A (Mod.act (equivalence.functor.obj M).X) S
        (pureTensor A _ _ S (groupGenerator A G S g) m)) =
      M.act S g (onSections A (underlying.hom.app M) S m)


  /-- The inverse equivalence restricts the module action to the same generators.
  Its underlying comparison is the counit followed by the forgetful comparison. -/
  inverse_action : ∀ (N : Mod (Modules A) (algebra A G)) (S : Profinite.{u})
      (g : C(S, G)) (m : sectionModule A (equivalence.inverse.obj N).module S),
    onSections A (equivalence.counitIso.app N).hom.hom S
      (onSections A (underlying.inv.app (equivalence.inverse.obj N)) S
        ((equivalence.inverse.obj N).act S g m)) =
      onSections A (Mod.act N.X) S
        (pureTensor A _ _ S (groupGenerator A G S g)
          (onSections A (equivalence.counitIso.app N).hom.hom S
            (onSections A (underlying.inv.app (equivalence.inverse.obj N)) S m)))

/-- Every action extends uniquely to the internal tensor. This is extension from the
free presheaf through module sheafification; it does not assert global freeness of sections.
Source: paragraph (3), internal bar input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: form the natural sectionwise bilinear map sum a_g[g],m maps to sum a_g(gm).
Use lem-sfb-condensed-free-linearization-tensor to identify the free module sheafification.
Apply lem-pc-sites-module-sheafification-bilinear-extension to extend it uniquely, then
lem-pc-sites-sheaf-tensor-bilinear-universal and lem-pe-internal-section-tensor-comparison
identify this bilinear extension with one unique internal relative-tensor map. -/
theorem action_extension (M : ActionModule A G) :
    ∃! γ : algebra A G ⊗ M.module ⟶ M.module,
      ∀ (S : Profinite.{u}) (g : C(S, G)) (m : sectionModule A M.module S),
        onSections A γ S (pureTensor A _ _ S (groupGenerator A G S g) m) =
          M.act S g m := by
  sorry

/-- The coefficient ring of sections, read through the fixed dependency interface.
Source: paragraph (3), bilinear extension
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
abbrev scalars (S : Profinite.{u}) :=
  (InternalAbelianSheafModule.sectionRings
    (coherentTopology Profinite.{u}) A.X).obj (op S)

/-- The unique bilinear sheaf extension agrees with finite free-presheaf sums and
with the internal tensor action on all pure tensors. Source: paragraph (3), the
explicit sheafification characterization
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: the finite sum formula defines a natural bilinear map on the free presheaf
and the section module. Apply module-sheafification bilinear extension and its
uniqueness, identifying the free sheaf by the free-linearization lemma. The internal
section-tensor comparison and the tensor universal property identify the extension
with the unique internal action. Linearity gives the displayed finite-sum formula;
only the presheaf generators are used, not global finite expressions for sheaf sections. -/
theorem bilinear_extension (M : ActionModule A G) :
    ∃! b : ∀ S : Profinite.{u},
      sectionModule A (algebra A G) S →ₗ[scalars A S]
        sectionModule A M.module S →ₗ[scalars A S] sectionModule A M.module S,
      (∀ (S T : Profinite.{u}) (f : T ⟶ S)
          (x : sectionModule A (algebra A G) S) (m : sectionModule A M.module S),
        (M.module.X.obj.map f.op).hom (b S x m) =
          b T (((algebra A G).X.obj.map f.op).hom x) ((M.module.X.obj.map f.op).hom m)) ∧
      (∀ (S : Profinite.{u}) (g : C(S, G)) (m : sectionModule A M.module S),
        b S (groupGenerator A G S g) m = M.act S g m) ∧
      (∀ (S : Profinite.{u}) (n : ℕ) (c : Fin n → scalars A S)
          (g : Fin n → C(S, G)) (m : sectionModule A M.module S),
        b S (∑ i : Fin n, c i • groupGenerator A G S (g i)) m =
          ∑ i : Fin n, c i • M.act S (g i) m) ∧
      (∃ γ : algebra A G ⊗ M.module ⟶ M.module,
        ∀ (S : Profinite.{u}) (x : sectionModule A (algebra A G) S)
            (m : sectionModule A M.module S),
          onSections A γ S (pureTensor A _ _ S x m) = b S x m) := by
  sorry

/-- The group algebra is a possibly noncommutative monoid with the normalized equivalence.
Source: paragraph (3), internal bar input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: linearize multiplication K times K to K and the identity section using
lem-sfb-condensed-free-linearization-tensor. Associativity and both unit laws follow
on generators from the group laws. Extend each given group action by action_extension.
Module associativity follows on [(g,h)],m and extends by bilinear sheafification uniqueness;
unitality follows on [1],m. Conversely restrict the algebra action to [g],m. The module
laws give a natural linear group action, with inverse given by g inverse. The two
constructions are inverse on objects and maps by the same bilinear extension uniqueness;
their unit and counit are underlying identities. This proves the normalized equivalence. -/
theorem exists_algebraEquivalence : Nonempty (AlgebraEquivalence A G) := by
  sorry


/-- Forgetting the action is additive, with the fixed sectionwise additive structures.
Source: paragraph (3), tensor and exactness input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: the functor retains the underlying maps, so it retains their sums and zero. -/
@[instance] theorem forget_additive : (forgetAction (R := A) (P := G)).Additive := by
  sorry

/-- The action category is abelian for its already specified preadditive structure.
Source: paragraph (3), exact-forgetful input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: lem-sfb-condensed-action-injective-infrastructure identifies the category with
module sheaves on the action site. Transport its abelian structure through that
additive equivalence, retaining the prescribed addition of maps. -/
theorem exists_abelian : ∃ h : Abelian (ActionModule A G),
    h.toPreadditive = (inferInstance : Preadditive (ActionModule A G)) := by
  sorry

/-- Forgetting creates the kernels and cokernels of every equivariant arrow.
Source: paragraph (3), exact-forgetful input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: use lem-sfb-condensed-action-injective-infrastructure. Kernels have restricted
section actions. Cokernels are sheafifications of sectionwise cokernels with the
unique action supplied by lem-sfb-equivariant-module-sheafification-reflector.
The universal lifts are equivariant since their composites with the kernel inclusion
or cokernel projection are equivariant. The underlying universal properties reflect
these limits and colimits. Cokernel projections need not be surjective on sections. -/
theorem creates_kernels_cokernels (M N : ActionModule A G) (f : M ⟶ N) :
    Nonempty (CreatesLimit (parallelPair f 0) (forgetAction (R := A) (P := G))) ∧
    Nonempty (CreatesColimit (parallelPair f 0) (forgetAction (R := A) (P := G))) := by
  sorry

/-- A lift of a specified underlying image factorization, normalized on both arrows.
Source: paragraph (3), image creation
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
structure ImageLift {M N : ActionModule A G} (f : M ⟶ N)
    (F : MonoFactorisation f.val) where
  /-- The equivariant factorization. -/
  factorization : MonoFactorisation f
  /-- Its middle object is the specified underlying image. -/
  underlying : factorization.I.module ≅ F.I
  /-- Its inclusion is the original image inclusion. -/
  inclusion : factorization.m.val = underlying.hom ≫ F.m
  /-- Its projection is the original image projection. -/
  projection : factorization.e.val ≫ underlying.hom = F.e
  /-- It is an image in the equivariant category. -/
  isImage : IsImage factorization

/-- Every underlying image lifts to an equivariant image.
Source: paragraph (3), exact-forgetful input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: form the equivariant kernel of the equivariant cokernel. Creation of kernels
and cokernels identifies its underlying object with the image of the underlying map.
Transfer along the unique image isomorphism to the specified factorization. Its
universal property follows from the underlying one and equivariance of the lifts. -/
theorem creates_images (M N : ActionModule A G) (f : M ⟶ N)
    (F : MonoFactorisation f.val) (hF : IsImage F) : Nonempty (ImageLift A G f F) := by
  sorry

/-- Actions on a fixed underlying subobject or quotient are uniquely induced.
Source: paragraph (3), exact-forgetful input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: for a monomorphism, cancel the inclusion in the equivariance equations.
For an epimorphism, local lifts along the quotient projection give the same equation
on all sections of the quotient. Sheaf-local equality then proves equality of actions.
This applies in particular to the kernels, cokernels and images just constructed. -/
theorem induced_action_unique (M N N' : ActionModule A G) (e : N.module = N'.module) :
    (∀ (i : N.module ⟶ M.module) [Mono i],
      Equivariant N M i → Equivariant N' M (eqToHom e.symm ≫ i) → HEq N.act N'.act) ∧
    (∀ (q : M.module ⟶ N.module) [Epi q],
      Equivariant M N q → Equivariant M N' (q ≫ eqToHom e) → HEq N.act N'.act) := by
  sorry

/-- Exactness in every degree and epimorphic augmentation are detected after forgetting.
Source: paragraph (3), exact-forgetful input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: in each degree exactness is equality of image and kernel. The created images
and kernels identify this with the same equality internally after forgetting.
An augmentation is epic exactly when its cokernel is zero; created cokernels and
reflection of zero objects give the second assertion. Apply the first assertion to
each consecutive pair of arrows of any equivariant complex, including its augmentation. -/
theorem exact_iff :
    (∀ S : ShortComplex (ActionModule A G),
      S.Exact ↔ (S.map (forgetAction (R := A) (P := G))).Exact) ∧
    (∀ (M N : ActionModule A G) (f : M ⟶ N), Epi f ↔ Epi f.val) := by
  sorry

/-- Linearization of a natural condensed-set action, on the actual free module.
Source: paragraph (3), linearization input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: on the sectionwise free presheaf put g(sum a_x[x]) = sum a_x[gx].
The action laws and restriction compatibility hold on generators, hence on all finite
sums. The equivariant sheafification reflector supplies the action on its sheafification,
identified with the fixed free object by lem-sfb-condensed-free-linearization-tensor.
The generator formula is preserved by its sheafification unit. -/
theorem linearization_exists
    (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (a : ∀ S : Profinite.{u}, C(S, G) →* Function.End (X.obj.obj (op S)))
    (ha : ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, G)) (x : X.obj.obj (op S)),
      X.obj.map f.op (a S g x) = a T (g.comp f.hom.hom) (X.obj.map f.op x)) :
    ∃ L : ActionModule A G, ∃ e : L.module ≅ (free A).obj X,
      ∀ (S : Profinite.{u}) (g : C(S, G)) (x : X.obj.obj (op S)),
        L.act S g (onSections A e.inv S (freeGenerator A X S x)) =
          onSections A e.inv S (freeGenerator A X S (a S g x)) := by
  sorry

/-- Equivariance of maps out of a linearized set is detected on generalized generators.
Source: paragraph (3), linearization input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: the equivariance equation compares maps A[G] tensor A[X] to M. Identify their
source with A[G times X] using lem-sfb-condensed-free-linearization-tensor. Its
free adjunction detects equality on every generalized pair (g,x), giving exactly
the displayed equation. This does not assume sections are globally free. -/
theorem equivariant_iff_on_generators
    (X : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (L M : ActionModule A G) (e : L.module ≅ (free A).obj X) (f : L.module ⟶ M.module) :
    Equivariant L M f ↔
      ∀ (S : Profinite.{u}) (g : C(S, G)) (x : X.obj.obj (op S)),
        onSections A f S (L.act S g (onSections A e.inv S (freeGenerator A X S x))) =
          M.act S g (onSections A f S (onSections A e.inv S (freeGenerator A X S x))) := by
  sorry

/-- Linearization carries every equivariant map of condensed sets to an equivariant map.
Source: paragraph (3), linearization input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: on a generalized generator the two composites are [u(gx)] and [g u(x)].
They agree by the assumed equivariance of u. The preceding generator criterion
extends their equality to the internal maps. -/
theorem linearization_map
    (X Y : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (a : ∀ S : Profinite.{u}, C(S, G) →* Function.End (X.obj.obj (op S)))
    (b : ∀ S : Profinite.{u}, C(S, G) →* Function.End (Y.obj.obj (op S)))
    (L K : ActionModule A G) (e : L.module ≅ (free A).obj X)
    (d : K.module ≅ (free A).obj Y)
    (hL : ∀ (S : Profinite.{u}) (g : C(S, G)) (x : X.obj.obj (op S)),
      L.act S g (onSections A e.inv S (freeGenerator A X S x)) =
        onSections A e.inv S (freeGenerator A X S (a S g x)))
    (hK : ∀ (S : Profinite.{u}) (g : C(S, G)) (y : Y.obj.obj (op S)),
      K.act S g (onSections A d.inv S (freeGenerator A Y S y)) =
        onSections A d.inv S (freeGenerator A Y S (b S g y)))
    (v : X ⟶ Y)
    (hv : ∀ (S : Profinite.{u}) (g : C(S, G)) (x : X.obj.obj (op S)),
      v.hom.app (op S) (a S g x) = b S g (v.hom.app (op S) x)) :
    Equivariant L K (e.hom ≫ (free A).map v ≫ d.inv) := by
  sorry

/-- The normalized tensor action, functorial in the acted-on factor and in every map
of trivially acted-on factors. Source: paragraph (3), tensor-action input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful). -/
structure TensorActions where
  /-- Tensor by an arbitrary module, with trivial action on that factor. -/
  functor : Modules A → ActionModule A G ⥤ ActionModule A G
  /-- The actual underlying tensor functor. -/
  underlying : ∀ T : Modules A,
    functor T ⋙ forgetAction ≅ forgetAction ⋙ tensorRight T
  /-- The induced tensor functor preserves addition of equivariant maps. -/
  additive : ∀ T : Modules A, (functor T).Additive
  /-- Its natural action is g(m tensor t) = gm tensor t. -/
  action : ∀ (T : Modules A) (M : ActionModule A G) (S : Profinite.{u}) (g : C(S, G))
      (m : sectionModule A M.module S) (t : sectionModule A T S),
    (functor T |>.obj M).act S g
        (onSections A ((underlying T).inv.app M) S (pureTensor A _ _ S m t)) =
      onSections A ((underlying T).inv.app M) S (pureTensor A _ _ S (M.act S g m) t)
  /-- Equivariant maps tensor with all linear maps between trivial factors. -/
  maps : ∀ (T T' : Modules A) (M N : ActionModule A G) (f : M ⟶ N) (t : T ⟶ T'),
    Equivariant ((functor T).obj M) ((functor T').obj N)
      (((underlying T).hom.app M) ≫ (f.val ⊗ₘ t) ≫ ((underlying T').inv.app N))

/-- Tensoring with a trivial action gives the natural additive tensor functor.
Source: paragraph (3), tensor-action input
(blueprint: lem-sfb-condensed-group-algebra-exact-forgetful).
Proof: on the sectionwise balanced tensor put g(m tensor t) = gm tensor t.
Linearity of g makes this balanced; the action laws and naturality hold on pure tensors.
Use lem-sfb-equivariant-module-sheafification-reflector and the normalized internal
section-tensor comparison to obtain the internal action. Tensor maps commute with
this action on pure tensors. The bilinear universal property extends that equality,
and the equations (f+f') tensor 1 = f tensor 1 + f' tensor 1 and 0 tensor 1 = 0,
to the sheafified tensor. No flatness assumption on the trivial factor is needed. -/
theorem exists_tensorActions : Nonempty (TensorActions A G) := by
  sorry

end Profinite.CondensedAction.GroupAlgebra
