/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePushforwardAtlasEqualizer
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyAffineSections
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Flat base change for algebraic-space module direct images

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 073K(1), degree zero;
Morphisms of Algebraic Spaces, Tag 073C; Modules on Sites, Tag 03D7
(blueprint: lem-sfb-space-flat-direct-image-base-change).

The pullback comparison is fixed by its action on local tensors. The base-change
transformation is its counit mate under the specified module adjunctions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z X' Y' : AlgebraicSpace S}

/-- The triangle for two successive charts, with the composite map of schemes.
Source: Stacks, Tag 03D7, tensor associativity
(blueprint: lem-sfb-space-flat-direct-image-base-change).
Proof: compose the two chart triangles. Functoriality of Yoneda and associativity
identify the resulting triangle with the chart triangle for the composite map. -/
theorem moduleCompositeChart_triangle (a : X ⟶ Y) (b : Y ⟶ Z)
    (V : Z.EtaleSite) (q : ModuleChart b V) (r : ModuleChart a q.left) :
    yoneda.map (r.hom.left ≫ q.hom.left) ≫ V.obj.hom =
      ((moduleChartTarget (a ≫ b)).obj r.left).hom := by
  sorry

/-- Compose the actual scheme maps of two successive module charts.
Source: Stacks, Tag 03D7 (blueprint: lem-sfb-space-flat-direct-image-base-change). -/
def moduleCompositeChart (a : X ⟶ Y) (b : Y ⟶ Z)
    (V : Z.EtaleSite) (q : ModuleChart b V) (r : ModuleChart a q.left) :
    ModuleChart (a ≫ b) V :=
  CostructuredArrow.mk (Y := r.left)
    (CostructuredArrow.homMk (r.hom.left ≫ q.hom.left)
      (moduleCompositeChart_triangle a b V q r))

/-- Tensor associativity uniquely specifies the composition comparison, including its
normalization relative to the chosen units. The inner scalar is pulled back along the
actual scheme map of the outer chart.
Source: Stacks, Tag 03D7 and Tag 03G8
(blueprint: lem-sfb-space-flat-direct-image-base-change).
Proof: on the canonical enlarged ringed sites, both iterated tensor pullback and
pullback along the composite are extension of scalars of the same inverse image.
Associativity sends c tensor (d tensor m) to c times a-sharp(d) tensor m; its
inverse inserts 1 in the inner tensor factor. Balancing proves the two inverse
identities. Sheafification glues these formulas, which commute with restrictions
and module morphisms. Every local section is locally a sum of such tensors, so
the formula uniquely determines the natural isomorphism. The chosen adjunction
units identify these local tensors with moduleTensorSection. -/
theorem moduleTensorComposition_existsUnique (a : X ⟶ Y) (b : Y ⟶ Z) :
    ∃! e : moduleTensorPullback b ⋙ moduleTensorPullback a ≅
        moduleTensorPullback (a ≫ b),
      ∀ (M : Z.Modules) (V : Z.EtaleSite) (q : ModuleChart b V)
        (r : ModuleChart a q.left)
        (c : X.structureSheaf.obj.obj (op r.left))
        (d : Y.structureSheaf.obj.obj (op q.left)) (m : M.val.obj (op V)),
        (e.hom.app M).val.app (op r.left)
            (moduleTensorSection a ((moduleTensorPullback b).obj M) q.left r c
              (moduleTensorSection b M V q d m)) =
          moduleTensorSection (a ≫ b) M V (moduleCompositeChart a b V q r)
            (c * moduleChartScalar a q.left r d) m := by
  sorry

/-- The uniquely tensor-normalized composition comparison; no unnormalized iso is chosen.
Source: Stacks, Tags 03D7 and 03G8
(blueprint: lem-sfb-space-flat-direct-image-base-change). -/
def moduleTensorComposition (a : X ⟶ Y) (b : Y ⟶ Z) :
    moduleTensorPullback b ⋙ moduleTensorPullback a ≅ moduleTensorPullback (a ≫ b) :=
  Classical.choose (moduleTensorComposition_existsUnique a b)

/-- The canonical comparison f'-star g-star to h-star f-star of a commuting square.
Source: Stacks, Tags 03D7 and 073K
(blueprint: lem-sfb-space-flat-direct-image-base-change). -/
def moduleTensorSquare (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (w : h ≫ f = f' ≫ g) :
    moduleTensorPullback g ⋙ moduleTensorPullback f' ≅
      moduleTensorPullback f ⋙ moduleTensorPullback h :=
  moduleTensorComposition f' g ≪≫
    eqToIso (congrArg moduleTensorPullback w.symm) ≪≫ (moduleTensorComposition h f).symm

/-- The counit composite whose adjoint is the ordinary base-change transformation.
Source: Stacks, Tag 073K(1), degree zero, and Tag 03D7
(blueprint: lem-sfb-space-flat-direct-image-base-change). -/
def moduleBaseChangeCounit (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (w : h ≫ f = f' ≫ g) :
    (moduleDirectImage f ⋙ moduleTensorPullback g) ⋙ moduleTensorPullback f' ⟶
      moduleTensorPullback h :=
  (Functor.associator _ _ _).hom ≫
    whiskerLeft (moduleDirectImage f) (moduleTensorSquare f g h f' w).hom ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (moduleTensorAdjunction f).counit (moduleTensorPullback h) ≫
    (Functor.leftUnitor _).hom

/-- The canonical base-change map, as a natural transformation on ALL module sheaves.
It is the adjoint of the comparison followed by h-star of the prescribed counit.
Source: Stacks, Tag 073K(1), degree zero; Tag 03D7
(blueprint: lem-sfb-space-flat-direct-image-base-change). -/
def moduleBaseChange (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (w : h ≫ f = f' ≫ g) :
    moduleDirectImage f ⋙ moduleTensorPullback g ⟶
      moduleTensorPullback h ⋙ moduleDirectImage f' :=
  ((moduleTensorAdjunction f').whiskerRight X.Modules).homEquiv _ _
    (moduleBaseChangeCounit f g h f' w)

/-- Flat base change for the specified ordinary module direct image from an algebraic
space to a scheme. The pullback square may be represented by any algebraic-space fibre
product. The map is natural in M by its definition as moduleBaseChange.
No finite-presentation, coherence, properness or Noetherian condition is imposed.
Source: Stacks, Tag 073K(1), i = 0, and Tag 073C
(blueprint: lem-sfb-space-flat-direct-image-base-change).

Proof:
1. Put N = f_* M. The quasi-compact separated pushforward theorem makes N
   quasi-coherent. Cover the target by affine V = Spec A, its base change by affine
   W = Spec B, and test on affine etale Z = Spec D over W. Flatness of g, etale
   flatness and composition make A to D flat. Isomorphisms can be tested on these
   covering tests, since local inverses agree and glue by the sheaf condition.
2. Etale module pushforward restriction reduces to X over V. Quasi-compactness
   gives a quasi-compact scheme atlas; finite affine atlas refinement makes its
   source U affine. The separated affine chart overlap theorem makes R = U x_X U
   affine. The two scheme maps U to V and R to V are quasi-compact separated.
3. The atlas equalizer identifies N(V) with ker(delta : P to Q), where P and Q
   are the sections on U and R, and delta is the difference of their restrictions.
   Kernels of module sheaves are evaluated objectwise by the sheaf gluing axiom.
4. Base-change the atlas to Z. Fibre products preserve etale covers; U_D and R_D
   are affine by the affine-spectrum fibre-product formula. Pullback preserves
   quasi-coherence. The same atlas equalizer computes the target sections.
5. The scheme Zariski/etale quasi-coherent equivalence and flat affine base-change
   sections theorem identify those two section modules with D tensor_A P and
   D tensor_A Q, by d tensor s mapping to d times the pulled-back section.
   Tensor associativity identifies the pullbacks, and delta_D = 1 tensor delta
   since both maps agree on pure tensors.
6. Flat tensor exactness identifies D tensor_A ker(delta) with ker(delta_D),
   bijectively and through the actual kernel arrows. This gives theta_D.
7. The affine pullback-section formula identifies (g-star N)(Z) with
   D tensor_B (B tensor_A N(V)) = D tensor_A N(V). Etale direct-image restriction
   identifies the target with the sections on X_Z, using the prescribed units.
8. The counit evaluates each compatible section on its chart. Thus the mate
   moduleBaseChange sends d tensor s to the same atlas section as theta_D.
   Atlas restriction is injective, so the maps agree and are isomorphisms on all
   covering affine tests. Their inverses glue. For a map M to M-tilde, both paths
   send d tensor s to d times the pullback of its image, proving naturality.
The proof dependencies and their detailed source places are recorded in the node. -/
theorem isIso_moduleBaseChange_of_flat
    {T T' : Over S} (g : T' ⟶ T) [Flat g.left]
    (f : X ⟶ schemeSpace T) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace T')
    (hp : IsPullback h.hom f'.hom f.hom ((Scheme.fppfTopology.over S).yoneda.map g))
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hsep : IsSeparatedPresheafMap f.hom.hom)
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((moduleBaseChange f
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace T' ⟶ schemeSpace T) h f'
      (ObjectProperty.hom_ext _ hp.w)).app M) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
