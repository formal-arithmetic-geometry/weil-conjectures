module

public import Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer
public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.NumberTheory.Padics.FiniteSubfieldContinuousLinearRetraction
import Sheaf.RepresentationTheory.LocalNormAlgclCocycleDescent

/-! # Finite-subextension continuous cochains

Source: latest Weil blueprint, six-functors direct-images proof, paragraph (3),
agent arithmetic coefficient-topology expansion; continuous cochains: Stacks Tag 0DVG;
ordinary derived localization: Stacks Tag 05RU.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism).

The submodules and their inclusion have explicit data. Cohomology is taken in abstract
modules, without closing images. Extending the underlying abelian-group complexes by
zero in negative degrees gives the actual arrow localized in the final theorem.
-/

@[expose] public section
set_option autoImplicit false
universe u v w x
open CategoryTheory
open scoped TensorProduct
namespace ContinuousCohomology
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[l] Ω] (E : IntermediateField ℚ_[l] Ω)
  (G : ProfiniteGrp.{v}) (W : Type w) [AddCommGroup W] [Module E W]
  (ρ : G →* (W ≃ₗ[E] W))

/-- The scalar-extended action on the actual tensor product, with its module topology
over Ω (the finite product norm topology in any basis of W). The action is the existing
`Representation.coefficientScalarExtension`, restricted to E.
Source: latest blueprint, direct-images (3), scalar-extension construction.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable def finiteScalarTopRep : TopRep E G := by
  letI : TopologicalSpace (Ω ⊗[E] W) := moduleTopology Ω (Ω ⊗[E] W)
  letI := IsModuleTopology.topologicalAddGroup Ω (Ω ⊗[E] W)
  letI : ContinuousSMul E (Ω ⊗[E] W) := ⟨by
    change Continuous (fun p : E × (Ω ⊗[E] W) ↦
      (algebraMap E Ω p.1) • p.2)
    exact
      (continuous_subtype_val.comp continuous_fst).smul
        (continuous_snd : Continuous (fun p : E × (Ω ⊗[E] W) ↦ p.2))⟩
  exact TopRep.of ⟨
    { toFun := fun g ↦
        { toLinearMap := (Representation.coefficientScalarExtension E Ω G W ρ g).toLinearMap
            |>.restrictScalars E
          cont := IsModuleTopology.continuous_of_linearMap
            (Representation.coefficientScalarExtension E Ω G W ρ g).toLinearMap }
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp }⟩

variable [hΩ : IsAlgClosure ℚ_[l] Ω] [FiniteDimensional ℚ_[l] E]
  (hρ : Representation.IsContinuousCoefficient l E G W ρ)

include hρ in
/-- The scalar-extended action is jointly continuous.
Source: latest blueprint, direct-images (3), first proof step.
Proof: choose a finite E-basis of W. Its action matrices are continuous by joint
continuity of the original action. After extension they have the same entries in E;
finite sums of products of continuous matrix entries and coordinates are continuous.
The zero-dimensional case is the unique map to the zero vector space.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
theorem finiteScalarTopRep_jointlyContinuous :
    Continuous (fun p : G × finiteScalarTopRep l Ω E G W ρ ↦
      (finiteScalarTopRep l Ω E G W ρ).ρ p.1 p.2) := by
  sorry

/-- The dependency's nonnegative continuous inhomogeneous complex, specialized to the
specified scalar-extended coefficients. Degree zero is functions on the singleton G^0.
Source: Stacks Tag 0DVG and latest blueprint, direct-images (3).
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable abbrev scalarContinuousComplex :=
  continuousInhomogeneousComplex (finiteScalarTopRep l Ω E G W ρ)
    (finiteScalarTopRep_jointlyContinuous l Ω E G W ρ hρ)

/-- Continuous ambient cochains with all values in the image of one fixed F tensor W.
The topology on this subspace is the finite-product subspace topology, so this agrees
with continuous F tensor W valued cochains, not merely pointwise algebraic functions.
Source: latest blueprint, direct-images (3), first proof step.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable def finiteFieldCochains (n : ℕ) (F : IntermediateField E Ω) :
    Submodule E ((scalarContinuousComplex l Ω E G W ρ hρ).X n) where
  carrier := {f | ∀ g, f g ∈ LinearMap.range
    (TensorProduct.map (IsScalarTower.toAlgHom E F Ω).toLinearMap
      (LinearMap.id : W →ₗ[E] W))}
  zero_mem' := fun _ ↦ Submodule.zero_mem _
  add_mem' := fun hf hg x ↦ Submodule.add_mem _ (hf x) (hg x)
  smul_mem' := fun a _ hf x ↦ Submodule.smul_mem _ a (hf x)

/-- The union over finite intermediate fields, expressed as a supremum of submodules.
The membership theorem below identifies this supremum with a single common finite
field for every value of a cochain. Source: latest blueprint, direct-images (3), step 1.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable def finiteSubextensionCochains (n : ℕ) :
    Submodule E ((scalarContinuousComplex l Ω E G W ρ hρ).X n) :=
  ⨆ (F : IntermediateField E Ω) (_ : FiniteDimensional E F),
    finiteFieldCochains l Ω E G W ρ hρ n F

/-- A cochain in the finite-subextension term has one common finite field for all values.
Source: latest blueprint, direct-images (3), step 1.
Proof: two finite fields lie in their finite compositum. The finite-field submodules
therefore form a directed family. Membership in their supremum is membership in one
member, by the directed-supremum membership lemma for submodules.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
theorem mem_finiteSubextensionCochains (n : ℕ)
    (f : (scalarContinuousComplex l Ω E G W ρ hρ).X n) :
    f ∈ finiteSubextensionCochains l Ω E G W ρ hρ n ↔
      ∃ (F : IntermediateField E Ω) (_ : FiniteDimensional E F),
        f ∈ finiteFieldCochains l Ω E G W ρ hρ n F := by
  sorry

/-- The specified differential preserves the finite-subextension terms.
Source: Stacks Tag 0DVG and latest blueprint, direct-images (3), step 1.
Proof: the membership characterization supplies one finite F. The action is through
W, so preserves F tensor W. Every differential value is a finite sum of signed action
and evaluation terms in the same subspace. Thus the same F works for the differential.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
theorem finiteSubextensionCochains_d (n : ℕ)
    (f : (scalarContinuousComplex l Ω E G W ρ hρ).X n)
    (hf : f ∈ finiteSubextensionCochains l Ω E G W ρ hρ n) :
    (scalarContinuousComplex l Ω E G W ρ hρ).d n (n + 1) f ∈
      finiteSubextensionCochains l Ω E G W ρ hρ (n + 1) := by
  sorry

/-- The actual subcomplex, with restricted differentials. Square-zero follows by
restriction from the dependency's continuous complex.
Source: latest blueprint, direct-images (3), step 1; Stacks Tag 0DVG.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable def finiteSubextensionComplex : CochainComplex (ModuleCat.{max u v w} E) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of E (finiteSubextensionCochains l Ω E G W ρ hρ n))
    (fun n ↦ ModuleCat.ofHom
      (((scalarContinuousComplex l Ω E G W ρ hρ).d n (n + 1)).hom.restrict
        (fun f hf ↦ finiteSubextensionCochains_d l Ω E G W ρ hρ n f hf)))
    (fun n ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      exact DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom
          ((scalarContinuousComplex l Ω E G W ρ hρ).d_comp_d n (n + 1) (n + 1 + 1)))
        f.val)

/-- The actual subcomplex inclusion: every component is the submodule subtype map.
Source: latest blueprint, direct-images (3), finite-subextension comparison arrow.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable def finiteSubextensionInclusion :
    finiteSubextensionComplex l Ω E G W ρ hρ ⟶ scalarContinuousComplex l Ω E G W ρ hρ :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (finiteSubextensionCochains l Ω E G W ρ hρ n).subtype)
    (fun n ↦ by
      dsimp only [finiteSubextensionComplex]
      simp only [CochainComplex.of_d]
      rfl)

/-- The actual inclusion is a quasi-isomorphism, with its degree-zero identification,
finite-field primitive detection, and finite-field cocycle representatives in every
positive degree. Here n denotes degree n+1 in the two positive-degree clauses.
Source: latest blueprint, direct-images (3), agent arithmetic expansion; Stacks 0DVG.
Proof:
1. Choose an E-basis of W. Every vector has finitely many algebraic coordinates,
so lies in one finite field. Thus both degree-zero terms are Ω tensor W, and their
invariant kernels and the inclusion on them are identical. Negative terms are zero.
2. If a finite-field cocycle is db for a continuous ambient b, use
lem-sfb-finite-subfield-continuous-linear-retraction to retract Ω continuously and
E-linearly onto its finite field. Coordinatewise retraction commutes with the E-valued
action matrices and hence the differential (lem-sfb-finite-scalar-cochain-retraction).
Retracting b gives a primitive in that same finite field, including degree one.
3. For any ambient positive cocycle z, lem-sfb-local-norm-algcl-cocycle-descent gives
an open H, finite F, cocycle u and b with res(z)=u+db. Compactness makes m=[G:H]
finite and positive. Apply lem-sfb-continuous-cochain-finite-index-transfer, naturally
in the finite-field inclusion. For its homotopy k with dk+kd=cor res-m id,
m z=cor(u)+d(cor(b)-kz). Divide by m in characteristic-zero E. Thus m^-1 cor(u)
is a finite-field cocycle representing z. No completion or closure of images occurs.
4. These primitive and representative assertions give injectivity and surjectivity
on every abstract cohomology group, hence the asserted quasi-isomorphism.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
theorem finiteSubextensionInclusion_quasiIso
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : IntermediateField ℚ_[l] Ω) [FiniteDimensional ℚ_[l] E]
    (G : ProfiniteGrp.{v}) (W : Type w) [AddCommGroup W] [Module E W]
    (ρ : G →* (W ≃ₗ[E] W))
    (hρ : Representation.IsContinuousCoefficient l E G W ρ) :
    QuasiIso (finiteSubextensionInclusion l Ω E G W ρ hρ) ∧
    (∀ v : Ω ⊗[E] W,
      (∀ g : G, Representation.coefficientScalarExtension E Ω G W ρ g v = v) ↔
        ∃! f : finiteSubextensionCochains l Ω E G W ρ hρ 0,
          (scalarContinuousComplex l Ω E G W ρ hρ).d 0 1 f.val = 0 ∧
            ∀ g : Fin 0 → G, f.val g = v) ∧
    (∀ (n : ℕ) (z : (scalarContinuousComplex l Ω E G W ρ hρ).X (n + 1)),
      (scalarContinuousComplex l Ω E G W ρ hρ).d (n + 1) (n + 2) z = 0 →
      z ∈ finiteSubextensionCochains l Ω E G W ρ hρ (n + 1) →
      (∃ b : (scalarContinuousComplex l Ω E G W ρ hρ).X n,
        (scalarContinuousComplex l Ω E G W ρ hρ).d n (n + 1) b = z) →
      ∃ b : finiteSubextensionCochains l Ω E G W ρ hρ n,
        (scalarContinuousComplex l Ω E G W ρ hρ).d n (n + 1) b.val = z) ∧
    (∀ (n : ℕ) (z : (scalarContinuousComplex l Ω E G W ρ hρ).X (n + 1)),
      (scalarContinuousComplex l Ω E G W ρ hρ).d (n + 1) (n + 2) z = 0 →
      ∃ (c : finiteSubextensionCochains l Ω E G W ρ hρ (n + 1))
        (b : (scalarContinuousComplex l Ω E G W ρ hρ).X n),
        (scalarContinuousComplex l Ω E G W ρ hρ).d (n + 1) (n + 2) c.val = 0 ∧
        z - c.val = (scalarContinuousComplex l Ω E G W ρ hρ).d n (n + 1) b) := by
  sorry

/-- Forget E-scalars in the actual inclusion and extend it by zero to integer degrees.
Source: latest blueprint, direct-images (3), step 4; Stacks Tag 05RU.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
noncomputable def finiteSubextensionInclusionAb :=
  HomologicalComplex.extendMap
    (((forget₂ (ModuleCat.{max u v w} E) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (finiteSubextensionInclusion l Ω E G W ρ hρ))
    ComplexShape.embeddingUpNat

/-- The localization of the actual inclusion is invertible in the ordinary D(Ab).
Source: latest blueprint, direct-images (3), step 4; Stacks Tag 05RU.
Proof: the preceding theorem gives isomorphisms on abstract cohomology. Forgetting
scalars is exact, and extension by zero preserves those cohomology maps, with zero
cohomology in negative degrees. The resulting integer complex arrow is therefore a
quasi-isomorphism. The derived localization inverts that arrow by its definition.
(blueprint: lem-sfb-finite-subextension-continuous-cochain-quasi-isomorphism). -/
theorem finiteSubextensionInclusion_derived_isIso
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : IntermediateField ℚ_[l] Ω) [FiniteDimensional ℚ_[l] E]
    (G : ProfiniteGrp.{v}) (W : Type w) [AddCommGroup W] [Module E W]
    (ρ : G →* (W ≃ₗ[E] W))
    (hρ : Representation.IsContinuousCoefficient l E G W ρ)
    [HasDerivedCategory.{x} AddCommGrpCat.{max u v w}] :
    IsIso (DerivedCategory.Q.map (finiteSubextensionInclusionAb l Ω E G W ρ hρ)) := by
  sorry

end ContinuousCohomology
