/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.AlgebraicGeometry.FppfSmallLocalRepresentatives

/-! # Quasi-coherent modules on the big fppf site of a scheme

Source: Stacks Project, Descent, Tags 03DX(1), 0GN7, 03LC(1), 06VE(3),(4),(7).
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- Forgetting algebraic operations preserves fppf sheaves without a size restriction.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: a matching family glues uniquely on each element. Uniqueness proves that the
glued function preserves every retained operation, yielding the required amalgamation. -/
@[instance] theorem sfbFppfCommRingToRing :
    fppfTopology.{u}.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- Forgetting algebraic operations preserves fppf sheaves without a size restriction.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: a matching family glues uniquely on each element. Uniqueness proves that the
glued function preserves every retained operation, yielding the required amalgamation. -/
@[instance] theorem sfbFppfCommRingToRingOver (S : Scheme.{u}) :
    (fppfTopology.over S).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- Forgetting algebraic operations preserves fppf sheaves without a size restriction.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: a matching family glues uniquely on each element. Uniqueness proves that the
glued function preserves every retained operation, yielding the required amalgamation. -/
@[instance] theorem sfbFppfCommRingToRingOverOver (S : Scheme.{u}) (T : Over S) :
    ((fppfTopology.over S).over T).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- Forgetting algebraic operations preserves fppf sheaves without a size restriction.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: a matching family glues uniquely on each element. Uniqueness proves that the
glued function preserves every retained operation, yielding the required amalgamation. -/
@[instance] theorem sfbFppfRingToAdd :
    fppfTopology.{u}.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  sorry

/-- Forgetting algebraic operations preserves fppf sheaves without a size restriction.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: a matching family glues uniquely on each element. Uniqueness proves that the
glued function preserves every retained operation, yielding the required amalgamation. -/
@[instance] theorem sfbFppfRingToAddOver (S : Scheme.{u}) :
    (fppfTopology.over S).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  sorry

/-- Forgetting algebraic operations preserves fppf sheaves without a size restriction.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: a matching family glues uniquely on each element. Uniqueness proves that the
glued function preserves every retained operation, yielding the required amalgamation. -/
@[instance] theorem sfbFppfRingToAddOverOver (S : Scheme.{u}) (T : Over S) :
    ((fppfTopology.over S).over T).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  sorry

/-- Small-valued additive sheafification on the big fppf site.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: sheafify in universe u+1 and use fppf_small_of_local_representatives to shrink
its sections to universe u. Transport addition and negation through the shrinking
bijections. Local uniqueness gives the additive universal property. -/
@[instance] theorem sfbFppfHasWeakSheafify (S : Scheme.{u}) :
    HasWeakSheafify (fppfTopology.over S) AddCommGrpCat.{u} := by
  sorry

/-- Local bijectivity detects additive sheafification equivalences.
Source: Stacks, Tag 00WK (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: compare the small-valued sheafification with the large-valued one by its
universal property. Local injectivity and surjectivity are unchanged by shrinking;
apply the usual large-valued characterization and reflect isomorphisms. -/
@[instance] theorem sfbFppfWEqualsLocallyBijective (S : Scheme.{u}) :
    (fppfTopology.over S).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- Additive sheafification on a slice of the big fppf site.
Source: Stacks, Tags 021S, 00WB (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: the equivalence (Sch/S)/T = Sch/T.left preserves fppf covers. Transport the
small-valued sheafification universal property along this equivalence. -/
@[instance] theorem sfbFppfOverHasWeakSheafify (S : Scheme.{u}) (T : Over S) :
    HasWeakSheafify ((fppfTopology.over S).over T) AddCommGrpCat.{u} := by
  sorry

/-- Local equivalences on slices of the big fppf site.
Source: Stacks, Tag 00WK (blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: the same cover-preserving slice equivalence identifies image and equalizer
sieves, so transport the locally bijective characterization on Sch/T.left. -/
@[instance] theorem sfbFppfOverWEqualsLocallyBijective (S : Scheme.{u}) (T : Over S) :
    ((fppfTopology.over S).over T).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  sorry

/-- Regular functions on the category of schemes as a ring sheaf.
Source: Stacks, Tag 03DU
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbGlobalFppfRings : Sheaf fppfTopology.{u} RingCat.{u} :=
  (sheafCompose fppfTopology.{u} (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (⟨Scheme.Γ, isSheaf_Γ fppfTopology⟩ : Sheaf fppfTopology.{u} CommRingCat.{u})

/-- Regular functions on the big fppf site, with the usual pullback of functions.
Source: Stacks, Tag 03DU
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbFppfStructureSheaf (V : Scheme.{u}) :
    Sheaf (fppfTopology.over V) CommRingCat.{u} :=
  Sheaf.over (⟨Scheme.Γ, isSheaf_Γ fppfTopology⟩ :
    Sheaf fppfTopology CommRingCat.{u}) V

/-- The same structure sheaf with commutativity forgotten.
Source: Stacks, Tag 03DU
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
abbrev sfbFppfRings (V : Scheme.{u}) :=
  (sheafCompose (fppfTopology.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (sfbFppfStructureSheaf V)

/-- All small ambient colimits exist on this ringed site.
Source: Stacks, Modules on Sites, abelian categories of modules; Descent, Tag 06VE
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: take sectionwise colimits of presheaves of modules and apply additive module
sheafification. Its universal property gives the colimit in sheaves of modules. -/
@[instance] theorem sfbFppfHasColimits (V : Scheme.{u}) :
    HasColimitsOfSize.{u, u} (ringedSiteModules.{u} (sfbFppfRings V)) := by
  sorry

/-- In particular, the ambient module category has cokernels.
Source: Stacks, Descent, Tag 06VE(4)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).
Proof: use the sectionwise cokernel presheaf and then module sheafification.
The sheafification adjunction identifies maps out with maps killing the original map. -/
@[instance] theorem sfbFppfHasCokernels (V : Scheme.{u}) :
    HasCokernels (ringedSiteModules.{u} (sfbFppfRings V)) := by
  sorry

/-- Zariski quasi-coherent modules, retaining every linear map.
Source: Stacks, Tag 03DX(1)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
abbrev SfbZariskiQCoh (V : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent V.ringCatSheaf).FullSubcategory

/-- Big-site quasi-coherent modules for the existing local-presentation predicate.
Source: Stacks, Tags 03DL, 03DX(1)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
abbrev SfbFppfQCoh (V : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent.{u} (sfbFppfRings V)).FullSubcategory

/-- Restrict a big-site module along postcomposition with a base map.
Source: Stacks, Tag 03LC(1)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbFppfRestrict {T V : Scheme.{u}} (f : T ⟶ V) :
    ringedSiteModules.{u} (sfbFppfRings V) ⥤ ringedSiteModules.{u} (sfbFppfRings T) :=
  SheafOfModules.overMap sfbGlobalFppfRings f

/-- The identity base map changes only the structure arrow of an object.
Source: Stacks, Tag 03LC(1)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbFppfIdArrow {V : Scheme.{u}} (U : Over V) :
    U ⟶ (Over.map (𝟙 V)).obj U :=
  Over.homMk (𝟙 U.left) (by simp)

/-- The associativity comparison between postcomposition functors.
Source: Stacks, Tag 03LC(1)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbFppfCompArrow {V T R : Scheme.{u}} (f : T ⟶ V) (g : R ⟶ T) (U : Over R) :
    (Over.map (g ≫ f)).obj U ⟶ (Over.map f).obj ((Over.map g).obj U) :=
  Over.homMk (𝟙 U.left) (by
    change (𝟙 U.left) ≫ ((U.hom ≫ g) ≫ f) = U.hom ≫ (g ≫ f)
    simp only [Category.id_comp, Category.assoc])

/-- Pullback of a global section, including restriction from the preimage of top.
Source: Stacks, Tags 03DR, 03DU
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbSectionPullback {T V : Scheme.{u}} (f : T ⟶ V) (M : V.Modules) :
    Γ(M, ⊤) ⟶ Γ((Modules.tensorPullback f).obj M, ⊤) :=
  ((Modules.tensorPullbackSectionAdjunction f).unit.app M).app ⊤ ≫
    ((Modules.tensorPullback f).obj M).presheaf.map (homOfLE f.preimage_top.ge).op

/-- Canonical global sections on an open subscheme, obtained from the same unit.
Source: Stacks, Tag 0GN7
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbOpenSection (V : Scheme.{u}) (M : V.Modules) (W : V.Opens) :
    Γ(M, W) ⟶ Γ((Modules.tensorPullback W.ι).obj M, ⊤) :=
  ((Modules.tensorPullbackSectionAdjunction W.ι).unit.app M).app W ≫
    ((Modules.tensorPullback W.ι).obj M).presheaf.map (homOfLE W.ι_preimage_self.ge).op

/-- Inclusion into all Zariski modules.
Source: Stacks, Tag 06VE
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbZariskiInclusion (V : Scheme.{u}) : SfbZariskiQCoh V ⥤ V.Modules :=
  (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι

/-- The associated functor regarded as taking values in all big-site modules.
Source: Stacks, Tag 06VE
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbAssociated (V : Scheme.{u}) (e : SfbZariskiQCoh V ≌ SfbFppfQCoh V) :
    SfbZariskiQCoh V ⥤ ringedSiteModules.{u} (sfbFppfRings V) :=
  e.functor ⋙ (SheafOfModules.isQuasicoherent (sfbFppfRings V)).ι

/-- The regular-module comparison of the normalized scheme pullback.
Source: Stacks, Tags 0096, 03DU
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence). -/
def sfbPullbackUnit {T V : Scheme.{u}} (f : T ⟶ V) :
    (Modules.tensorPullback f).obj (SheafOfModules.unit V.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  ((Modules.tensorPullbackSectionAdjunction f).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction f)).app _ ≪≫ Modules.pullbackObjUnitIso f

/-- The section formula defines the quasi-coherent big-fppf equivalence, its
restriction inverse, and its colimit and tensor comparisons.

Source: Stacks Project, Descent, Tags 03DX(1), 0GN7, 03LC(1), 06VE(3),(4),(7)
(blueprint: lem-sfb-scheme-big-fppf-quasicoherent-equivalence).

Proof (the node's nine steps):
1. Pullbacks of quasi-coherent modules remain quasi-coherent. An fppf cover is
fpqc; full faithfulness of fpqc descent glues sections, viewed as maps from O.
This proves sheafhood of the section formula, including scalars and module maps.
2. The big-fppf/Zariski ringed comparison identifies this already sheaf-valued
formula with ringed pullback. Module adjunction gives colimit preservation and
identifies the unit with the identity on opens; multiplication identifies A(O).
3. Present a small colimit as the cokernel of the arrow-relation map between
coproducts. Coproduct and cokernel closure keep it quasi-coherent. Apply step 2,
including to ambient cokernels.
4. Normalized composition of scheme pullbacks gives base restriction. On scalar
tensors the identity and composition comparisons multiply all scalar factors,
which proves their naturality and coherence.
5. On each affine open choose a presentation of the corresponding module by
arbitrary free modules. The tilde adjunction and its preservation of colimits,
then step 2, give site-local free presentations. The identity unit and module
adjunction give full faithfulness for all linear maps.
6. Conversely, lift each differential of a local free presentation uniquely by
full faithfulness, and take its quasi-coherent scheme cokernel. Step 3 identifies
its associated sheaf with the given sheaf locally.
7. Lift the overlap isomorphisms by full faithfulness. Faithfulness proves the
inverse equations and triple cocycle. Effective fpqc descent gives a scheme
module; pullback preserves quasi-coherence without any affineness of overlaps.
8. Glue the local maps and their inverses by sheaf-Hom gluing. Restriction to
opens identifies the inverse with the descended module. The identity unit and
the triangle identity make the canonical counit invertible with the same open
normalization. This yields the equivalence.
9. Tensor closure and the ringed-pullback tensor theorem give the tensor iso.
Its inverse sends two sections to their tensor after pullback: on local tensors
(a tensor m) tensor (b tensor n) it sends them to ab tensor (m tensor n).
Scalar balancing verifies both inverse composites; sheafification extends the
equations from local generators. No flatness or finiteness is used.

Dependencies by step:
1. lem-weil-pbc-module-pullback-quasi-coherent, lem-trf-fppf-covering-is-fpqc,
   lem-pc-fpqc-descent, lem-pc-module-pullback-identity-composition.
2. lem-sfb-big-fppf-zariski-ringed-comparison,
   lem-weil-pbc-ringed-topoi-module-adjunction,
   lem-weil-pbc-left-adjoint-preserves-colimits.
3. lem-weil-pbc-quasi-coherent-module-coproduct-closure,
   lem-weil-pbc-quasi-coherent-module-cokernel-closure.
4. lem-pc-module-pullback-identity-composition.
5. lem-weil-pbc-affine-tilde-gamma-adjunction, lem-weil-pbc-spec-tilde-free-module,
   lem-pc-zariski-coverings-are-fppf, lem-weil-pbc-module-pullback-quasi-coherent,
   def-trf-space-quasi-coherent-module, lem-weil-pbc-ringed-topoi-module-adjunction.
6. def-trf-space-quasi-coherent-module,
   lem-weil-pbc-quasi-coherent-module-coproduct-closure,
   lem-weil-pbc-quasi-coherent-module-cokernel-closure, lem-weil-pbc-spec-tilde-free-module.
7. lem-weil-pbc-module-pullback-quasi-coherent, lem-trf-fppf-covering-is-fpqc,
   lem-pc-fpqc-descent.
8. lem-pur-sheaf-hom-cover-gluing, lem-weil-pbc-ringed-topoi-module-adjunction,
   lem-sfb-big-fppf-zariski-ringed-comparison.
9. lem-weil-pbc-quasi-coherent-tensor-product-affine-sections,
   lem-weil-pbc-ringed-topoi-module-pullback-tensor,
   lem-weil-pbc-module-pullback-tensor, def-pur-sheaf-tensor-product.
-/
theorem scheme_big_fppf_quasicoherent_equivalence :
    ∃ e : ∀ V : Scheme.{u}, SfbZariskiQCoh V ≌ SfbFppfQCoh V,
    ∃ s : ∀ (V : Scheme.{u}) (M : SfbZariskiQCoh V) (U : Over V),
      ((sfbAssociated V (e V)).obj M).val.obj (op U) ≃+
        Γ((Modules.tensorPullback U.hom).obj M.obj, ⊤),
    ∃ r : ∀ (V : Scheme.{u}) (G : SfbFppfQCoh V) (W : V.Opens),
      Γ(((e V).inverse.obj G).obj, W) ≃+
        G.obj.val.obj (op (V.restrictFunctor.obj W)),
    ∃ q : ∀ (V T : Scheme.{u}) (f : T ⟶ V) (M : SfbZariskiQCoh V),
      SheafOfModules.IsQuasicoherent ((Modules.tensorPullback f).obj M.obj),
    ∃ b : ∀ (V T : Scheme.{u}) (f : T ⟶ V) (M : SfbZariskiQCoh V),
      (sfbFppfRestrict f).obj ((sfbAssociated V (e V)).obj M) ≅
        (sfbAssociated T (e T)).obj ⟨(Modules.tensorPullback f).obj M.obj, q V T f M⟩,
    (∀ (V : Scheme.{u}) (M : SfbZariskiQCoh V) (U : Over V)
      (a : Γ(U.left, ⊤)) (x : ((sfbAssociated V (e V)).obj M).val.obj (op U)),
      s V M U (a • x) = a • s V M U x) ∧
    (∀ (V : Scheme.{u}) (M : SfbZariskiQCoh V) (U U' : Over V) (h : U' ⟶ U)
      (x : ((sfbAssociated V (e V)).obj M).val.obj (op U)),
      s V M U' (((sfbAssociated V (e V)).obj M).val.map h.op x) =
        (eqToHom (congrArg (fun f ↦ (Modules.tensorPullback f).obj M.obj) h.w)).app ⊤
          (((Modules.tensorPullbackSectionComp h.left U.hom).inv.app M.obj).app ⊤
            (sfbSectionPullback h.left ((Modules.tensorPullback U.hom).obj M.obj)
              (s V M U x)))) ∧
    (∀ (V : Scheme.{u}) (M N : SfbZariskiQCoh V) (v : M ⟶ N) (U : Over V)
      (x : ((sfbAssociated V (e V)).obj M).val.obj (op U)),
      s V N U (((sfbAssociated V (e V)).map v).val.app (op U) x) =
        ((Modules.tensorPullback U.hom).map v.hom).app ⊤ (s V M U x)) ∧
    (∀ (V : Scheme.{u}) (G H : SfbFppfQCoh V) (v : G ⟶ H) (W : V.Opens)
      (x : Γ(((e V).inverse.obj G).obj, W)),
      r V H W (Modules.Hom.app ((e V).inverse.map v).hom W x) =
        v.hom.val.app (op (V.restrictFunctor.obj W)) (r V G W x)) ∧
    (∀ (V : Scheme.{u}) (G : SfbFppfQCoh V) (W : V.Opens)
      (a : Γ(V, W)) (x : Γ(((e V).inverse.obj G).obj, W)),
      r V G W (a • x) = W.topIso.inv a • r V G W x) ∧
    (∀ (V : Scheme.{u}) (G : SfbFppfQCoh V) (W W' : V.Opens) (i : W' ⟶ W)
      (x : Γ(((e V).inverse.obj G).obj, W)),
      r V G W' ((Modules.presheaf ((e V).inverse.obj G).obj).map i.op x) =
        G.obj.val.map (V.restrictFunctor.map i).op (r V G W x)) ∧
    (∀ (V : Scheme.{u}) (M : SfbZariskiQCoh V) (W : V.Opens) (x : Γ(M.obj, W)),
      r V ((e V).functor.obj M) W (Modules.Hom.app ((e V).unitIso.hom.app M).hom W x) =
        (s V M (V.restrictFunctor.obj W)).symm (sfbOpenSection V M.obj W x)) ∧
    (∀ (V : Scheme.{u}) (G : SfbFppfQCoh V) (W : V.Opens)
      (x : Γ(((e V).inverse.obj G).obj, W)),
      ((e V).counitIso.hom.app G).hom.val.app (op (V.restrictFunctor.obj W))
        ((s V ((e V).inverse.obj G) (V.restrictFunctor.obj W)).symm
          (sfbOpenSection V ((e V).inverse.obj G).obj W x)) = r V G W x) ∧
    (∀ (V T : Scheme.{u}) (f : T ⟶ V) (M : SfbZariskiQCoh V) (U : Over T)
      (x : ((sfbAssociated V (e V)).obj M).val.obj (op ((Over.map f).obj U))),
      s T ⟨(Modules.tensorPullback f).obj M.obj, q V T f M⟩ U
        ((b V T f M).hom.val.app (op U) x) =
        ((Modules.tensorPullbackSectionComp U.hom f).hom.app M.obj).app ⊤
          (s V M ((Over.map f).obj U) x)) ∧
    (∀ (V T : Scheme.{u}) (f : T ⟶ V) (M N : SfbZariskiQCoh V) (v : M ⟶ N),
      (sfbFppfRestrict f).map ((sfbAssociated V (e V)).map v) ≫ (b V T f N).hom =
        (b V T f M).hom ≫ (sfbAssociated T (e T)).map
          (ObjectProperty.homMk ((Modules.tensorPullback f).map v.hom))) ∧
    (∀ (V : Scheme.{u}) (M : SfbZariskiQCoh V) (U : Over V)
      (x : ((sfbAssociated V (e V)).obj M).val.obj (op ((Over.map (𝟙 V)).obj U))),
      ((sfbAssociated V (e V)).map
        (ObjectProperty.homMk ((Modules.tensorPullbackSectionId V).hom.app M.obj))).val.app
          (op U) ((b V V (𝟙 V) M).hom.val.app (op U) x) =
        ((sfbAssociated V (e V)).obj M).val.map (sfbFppfIdArrow U).op x) ∧
    (∀ (V T R : Scheme.{u}) (f : T ⟶ V) (g : R ⟶ T) (M : SfbZariskiQCoh V)
      (U : Over R)
      (x : ((sfbAssociated V (e V)).obj M).val.obj
        (op ((Over.map f).obj ((Over.map g).obj U)))),
      ((sfbAssociated R (e R)).map (ObjectProperty.homMk
        ((Modules.tensorPullbackSectionComp g f).hom.app M.obj))).val.app (op U)
          ((b V R (g ≫ f) M).hom.val.app (op U)
            (((sfbAssociated V (e V)).obj M).val.map (sfbFppfCompArrow f g U).op x)) =
        (b T R g ⟨(Modules.tensorPullback f).obj M.obj, q V T f M⟩).hom.val.app (op U)
          ((b V T f M).hom.val.app (op ((Over.map g).obj U)) x)) ∧
    (∀ (V : Scheme.{u}) (I : Type u) [SmallCategory I] (D : I ⥤ SfbZariskiQCoh V),
      ∃ h : SheafOfModules.IsQuasicoherent (colimit (D ⋙ sfbZariskiInclusion V)),
      ∃ c : (sfbAssociated V (e V)).obj ⟨colimit (D ⋙ sfbZariskiInclusion V), h⟩ ≅
        colimit (D ⋙ sfbAssociated V (e V)),
      ∀ i : I,
        (sfbAssociated V (e V)).map
          (ObjectProperty.homMk (colimit.ι (D ⋙ sfbZariskiInclusion V) i)) ≫ c.hom =
            colimit.ι (D ⋙ sfbAssociated V (e V)) i) ∧
    (∀ (V : Scheme.{u}) (M N : SfbZariskiQCoh V) (v : M ⟶ N),
      ∃ h : SheafOfModules.IsQuasicoherent (cokernel v.hom),
      ∃ c : (sfbAssociated V (e V)).obj ⟨cokernel v.hom, h⟩ ≅
        cokernel ((sfbAssociated V (e V)).map v),
      (sfbAssociated V (e V)).map (ObjectProperty.homMk (cokernel.π v.hom)) ≫ c.hom =
        cokernel.π ((sfbAssociated V (e V)).map v)) ∧
    (∀ V : Scheme.{u},
      ∃ h : SheafOfModules.IsQuasicoherent (SheafOfModules.unit V.ringCatSheaf),
      ∃ c : (sfbAssociated V (e V)).obj ⟨SheafOfModules.unit V.ringCatSheaf, h⟩ ≅
        SheafOfModules.unit (sfbFppfRings V),
      ∀ (U : Over V)
        (x : ((sfbAssociated V (e V)).obj ⟨SheafOfModules.unit V.ringCatSheaf, h⟩).val.obj
          (op U)),
      c.hom.val.app (op U) x = (sfbPullbackUnit U.hom).hom.app ⊤
        (s V ⟨SheafOfModules.unit V.ringCatSheaf, h⟩ U x)) ∧
    (∀ (V : Scheme.{u}) (M N : SfbZariskiQCoh V),
      ∃ h : SheafOfModules.IsQuasicoherent (M.obj ⊗ N.obj),
      ∃ c : (sfbAssociated V (e V)).obj ⟨M.obj ⊗ N.obj, h⟩ ≅
        (SheafOfModules.siteSheafTensorRight ((sfbAssociated V (e V)).obj N)).obj
          ((sfbAssociated V (e V)).obj M),
      ∃ p : ∀ U : Over V,
        (Modules.tensorPullback U.hom).obj (M.obj ⊗ N.obj) ≅
          (Modules.tensorPullback U.hom).obj M.obj ⊗
            (Modules.tensorPullback U.hom).obj N.obj,
      (∀ (U : Over V) (W : V.Opens) (x : Γ(M.obj, W)) (y : Γ(N.obj, W)),
        (p U).hom.app (U.hom ⁻¹ᵁ W)
          (Modules.tensorPullbackSection U.hom (M.obj ⊗ N.obj) W
            (Modules.tmulSection x y)) =
          Modules.tmulSection (Modules.tensorPullbackSection U.hom M.obj W x)
            (Modules.tensorPullbackSection U.hom N.obj W y)) ∧
      ∀ (U : Over V)
        (x : ((sfbAssociated V (e V)).obj M).val.obj (op U))
        (y : ((sfbAssociated V (e V)).obj N).val.obj (op U)),
        s V ⟨M.obj ⊗ N.obj, h⟩ U
          (c.inv.val.app (op U) (SheafOfModules.siteSheafTensorTmul
            ((sfbAssociated V (e V)).obj M) ((sfbAssociated V (e V)).obj N) (op U) x y)) =
          (p U).inv.app ⊤ (Modules.tmulSection (s V M U x) (s V N U y))) := by
  sorry

end AlgebraicGeometry.Scheme
