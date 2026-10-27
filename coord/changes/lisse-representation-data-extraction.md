# AlgebraicGeometry.ProEtale.LisseRepresentation

## Reason

Move the existing data interface into `Sheaf.Paper.LisseQlbarRepresentationDefs` so
independent proof-step modules can use it without importing their assembly theorem.
The item publicly re-exports this interface. All 36 existing data declarations, including
the quotient-finiteness instance, retain their exact text, names, signatures and bodies.
Only their owning module changes. The large normalization predicates are locally
irreducible while checking Conclusion, avoiding repeated expansion during linting.
Their exported transparency and exact declaration bodies remain unchanged. Proof-only
public imports are moved to the proof module, and unused statement imports are removed. This is an import-cycle prevention refactor, not a
response to compile-time limits. No declaration under WeilConjectures changes.

## Old

In `Sheaf.Paper.LisseQlbarRepresentations`:

```lean
/-- The actual internal modules over the recorded pulled-back coefficient ring.
Source: blueprint lisse-qlbar-representations, coefficient convention
(blueprint: thm-lisse-qlbar-representations). -/
abbrev Modules (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)

/-- Global sections after inverse image to the geometric point. Cartesian coefficients
identify this with the underlying sheaf of the recorded ringed-topos inverse image.
Source: blueprint lisse-qlbar-representations, Fibres
(blueprint: thm-lisse-qlbar-representations). -/
def pointSections {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  ProEtale.upperStar Ab.{u + 1} x ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))

/-- The actual additive geometric fibre, with no basis or representation chosen.
Source: blueprint lisse-qlbar-representations, Fibres
(blueprint: thm-lisse-qlbar-representations). -/
def fibre (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) :
    Modules Λ X ⥤ Ab.{u + 1} :=
  CondensedRing.upperStar Λ.X x ⋙ Mod.forget _ ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))

/-- The canonical underlying-sheaf comparison for cartesian coefficient pullback.
It is extension along the coefficient isomorphism followed by restriction along its inverse.
Source: blueprint Fibres; pulled-back coefficient convention
(blueprint: thm-lisse-qlbar-representations). -/
def fibreUnderlying (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) :
    fibre Λ x ≅ Mod.forget _ ⋙ pointSections x :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} x).mapMod _)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X x)))
    (Mod.forget _ ⋙ sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω))))))

/-- The canonical map on fibres of a coefficient-semilinear module map.
Source: blueprint lisse-qlbar-representations, coefficient compatibility
(blueprint: thm-lisse-qlbar-representations). -/
def fibreMap {Λ Μ : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Μ.X]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    {M : Modules Λ X} {N : Modules Μ X} (i : M.X ⟶ N.X) :
    (fibre Λ x).obj M ⟶ (fibre Μ x).obj N :=
  (fibreUnderlying Λ x).hom.app M ≫ (pointSections x).map i ≫
    (fibreUnderlying Μ x).inv.app N

/-- Constant sections of continuous coefficients, retaining the existing condensed ring.
Source: blueprint lisse-qlbar-representations, coefficients
(blueprint: thm-lisse-qlbar-representations). -/
def continuousConstants (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : R →+* Γ (Profinite.continuousMapRingObj.{u} R) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf R)
    (fun _ ↦ ULift.ringEquiv.symm.toRingHom.comp ContinuousMap.C) (fun _ _ ↦ rfl)

/-- Multiplication by a constant coefficient on the underlying module sheaf.
Source: blueprint lisse-qlbar-representations, coefficient convention
(blueprint: thm-lisse-qlbar-representations). -/
def scalarSheaf (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {R : Type} [CommRing R] (c : R →+* Γ Λ.X)
    (X : Scheme.{u}) (M : Modules Λ X) (r : R) : M.X ⟶ M.X :=
  (λ_ M.X).inv ≫
    ((Γ.mapFunctorMonoidHom (upperStarFromPoint X) (c r)).hom ⊗ₘ 𝟙 M.X) ≫ Mod.act M.X

/-- Scalar multiplication on the genuine geometric fibre, before choosing any basis.
Source: blueprint lisse-qlbar-representations, Fibres
(blueprint: thm-lisse-qlbar-representations). -/
def fibreScalar (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {R : Type} [CommRing R] (c : R →+* Γ Λ.X)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (M : Modules Λ X) (r : R) (v : (fibre Λ x).obj M) : (fibre Λ x).obj M :=
  (fibreMap (Λ := Λ) (Μ := Λ) (M := M) (N := M) x (scalarSheaf Λ c X M r)).hom v

/-- The invertible linear action, without restricting the coefficient universe.
Source: Weil II (1.1.6), the blueprint representation convention
(blueprint: thm-lisse-qlbar-representations). -/
def linearAction {R : Type} [CommRing R] {G : Type u} [Group G]
    (V : Rep.{u + 1} R G) : G →* (V.V ≃ₗ[R] V.V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V.V).toMonoidHom.comp
    (Representation.asGroupHom (k := R) (G := G) (V := V.V) V.ρ)

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- An equivalence onto the specified representations, with the actual additive fibre
and its scalar action fixed. Full faithfulness and the exact essential image are the
usual equivalence criterion; no lattice or basis is included in the source objects.
Source: blueprint lisse-qlbar-representations, clauses (1)--(3)
(blueprint: thm-lisse-qlbar-representations). -/
structure Correspondence (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (R : Type) [CommRing R] (c : R →+* Γ Λ.X)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (G : Type u) [Group G] (P : ObjectProperty (Modules Λ X))
    (Q : ObjectProperty (Rep.{u + 1} R G)) where
  functor : P.FullSubcategory ⥤ Rep.{u + 1} R G
  fullyFaithful : functor.FullyFaithful
  image : ∀ L, Q (functor.obj L)
  essentiallySurjective : ∀ V, Q V → ∃ L, Nonempty (functor.obj L ≅ V)
  comparison : functor ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ⋙
    forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1} ≅ ObjectProperty.ι P ⋙ fibre Λ x
  scalar : ∀ (L : P.FullSubcategory) (r : R) (v : (functor.obj L).V),
    (comparison.hom.app L).hom (r • v) =
      fibreScalar Λ c x L.obj r ((comparison.hom.app L).hom v)

/-- Freeness and finiteness refer to the actual scalar action on geometric sections.
Source: blueprint lisse-qlbar-representations, Fibres
(blueprint: thm-lisse-qlbar-representations). -/
def FiniteFreeFibre (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (R : Type) [CommRing R] (c : R →+* Γ Λ.X)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) : Prop :=
  ∀ M : Modules Λ X, IsLisseCoefficientModule Λ.X M →
    ∃ V : ModuleCat.{u + 1} R, Module.Free R V ∧ Module.Finite R V ∧
      ∃ e : (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}).obj V ≅ (fibre Λ x).obj M,
        ∀ (r : R) (v : V), e.hom (r • v) = fibreScalar Λ c x M r (e.hom v)

/-- A finite classical local system, viewed on the pro-etale site with its underlying
abelian sheaf. The universe lift does not change its finite coefficient ring.
Source: Stacks 099Y and blueprint lisse-qlbar-representations (1)
(blueprint: thm-lisse-qlbar-representations). -/
def classicalAb (A : Type) [CommRing A] (X : Scheme.{u}) :
    Scheme.LisseModuleSheafCategory X (ULift.{u + 1} A) ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  ObjectProperty.ι _ ⋙ comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X ⋙
    sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})

/-- A section on a pointed neighbourhood pulled back to the geometric point: apply the
actual adjunction unit and restrict along the displayed section of the base change.
Source: blueprint Fibres; Stacks 05V1
(blueprint: thm-lisse-qlbar-representations). -/
def pointGerm {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (H : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (U : X.ProEt) (a : Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ x).obj U) :
    H.obj.obj (op U) ⟶ (pointSections x).obj H :=
  ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} x).unit.app H).hom.app (op U) ≫
    ((ProEtale.upperStar Ab.{u + 1} x).obj H).obj.map a.op

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The comparison between classical geometric stalks and sections at the point is
normalized on every pointed etale germ. This excludes an arbitrary fibre isomorphism.
Source: blueprint Fibres; Stacks 05V1, 0993
(blueprint: thm-lisse-qlbar-representations). -/
structure FiniteFibreComparison (A : Type) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) where
  iso : classicalAb A X ⋙ pointSections x ≅
    ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale x).sheafFiber ⋙
      forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}
  germ : ∀ (F : Scheme.LisseModuleSheafCategory X (ULift.{u + 1} A)) (U : X.Etale)
      (z : (Scheme.pointSmallEtale x).fiber.obj U)
      (a : Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) ⟶
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ x).obj
          ((Scheme.toProEt X).obj U)),
    a.left ≫ pullback.fst U.hom x = z.left →
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}).map
        (((comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).unit.app
          F.obj).hom.app (op U)) ≫
        pointGerm x ((classicalAb A X).obj F) ((Scheme.toProEt X).obj U) a ≫
        iso.hom.app F =
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}).map
        ((Scheme.pointSmallEtale x).toPresheafFiber U z F.obj.obj)

/-- Extension of scalars of a representation along the actual coefficient homomorphism.
Source: blueprint lisse-qlbar-representations (2),(3), coefficient compatibility
(blueprint: thm-lisse-qlbar-representations). -/
def scalarRep {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (G : Type u) [Group G] : Rep.{u + 1} R G ⥤ Rep.{u + 1} S G :=
  (Rep.repIsoAction R G).functor ⋙
    (ModuleCat.ringExtendScalars.{0, u + 1} φ).mapAction G ⋙
      (Rep.repIsoAction S G).inverse

/-- All localization and model comparisons use the actual coefficient-change unit and
send pure tensors to scalar multiples of that unit on geometric sections. Quantifying
all presentations states lattice/model independence as well as scalar compatibility.
Source: blueprint lisse-qlbar-representations (2),(3), tensor/scalar paragraph
(blueprint: thm-lisse-qlbar-representations). -/
def ScalarCompatible
    {Λ Μ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X] [IsCommMonObj Μ.X]
    {R S : Type} [CommRing R] [CommRing S] {c : R →+* Γ Λ.X} {d : S →+* Γ Μ.X}
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] {x : Spec (.of Ω) ⟶ X}
    {G : Type u} [Group G] {P : ObjectProperty (Modules Λ X)}
    {Q : ObjectProperty (Rep.{u + 1} R G)} {P' : ObjectProperty (Modules Μ X)}
    {Q' : ObjectProperty (Rep.{u + 1} S G)}
    (C : Correspondence Λ R c x G P Q) (D : Correspondence Μ S d x G P' Q')
    (f : Λ.X ⟶ Μ.X) [IsMonHom f] (φ : R →+* S) : Prop :=
  (∀ M : P.FullSubcategory, P' ((Mod.extendScalars (coefficientMap f X)).obj M.obj)) ∧
  ∀ (M : P.FullSubcategory) (N : P'.FullSubcategory)
    (i : M.obj ⟶ (Mod.comap (coefficientMap f X)).obj N.obj),
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap f X)).homEquiv M.obj N.obj).symm i) →
      ∃ e : (scalarRep φ G).obj (C.functor.obj M) ≅ D.functor.obj N,
        ∀ (a : S) (v : (C.functor.obj M).V),
          (D.comparison.hom.app N).hom
            (e.hom.hom (ModuleCat.ringExtensionTmul φ
              (ModuleCat.of R (C.functor.obj M).V) a v)) =
          fibreScalar Μ d x N.obj a
            ((fibreMap (Λ := Λ) (Μ := Μ) (M := M.obj) (N := N.obj) x i.hom).hom
              ((C.comparison.hom.app M).hom v))

/-- The canonical pure tensor of two sections, using the sheafification unit and
its monoidal comparison. No identification with the presheaf tensor is assumed.
Source: blueprint lisse-qlbar-representations, tensor compatibility
(blueprint: thm-lisse-qlbar-representations). -/
def sheafTensorSection {X : Scheme.{u}}
    (F H : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (U : X.ProEt)
    (a : F.obj.obj (op U)) (b : H.obj.obj (op U)) : (F ⊗ H).obj.obj (op U) :=
  let ψ := (Functor.Monoidal.μIso
    (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) F.obj H.obj).inv ≫
    ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).counit.app F ⊗ₘ
      (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).counit.app H)
  let q := (toSheafify (Scheme.ProEt.topology X) (F.obj ⊗ H.obj)).app (op U) ≫ ψ.hom.app (op U)
  q.hom (a ⊗ₜ[ℤ] b)

/-- The canonical tensor of geometric fibre vectors, with the relative tensor projection
and the strong monoidal pullback comparison.
Source: blueprint lisse-qlbar-representations, tensor compatibility
(blueprint: thm-lisse-qlbar-representations). -/
def fibreTensor (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (M N : Modules Λ X) (a : (fibre Λ x).obj M) (b : (fibre Λ x).obj N) :
    (fibre Λ x).obj (M ⊗ N) :=
  let a' := ((fibreUnderlying Λ x).hom.app M).hom a
  let b' := ((fibreUnderlying Λ x).hom.app N).hom b
  let t := sheafTensorSection ((ProEtale.upperStar Ab.{u + 1} x).obj M.X)
    ((ProEtale.upperStar Ab.{u + 1} x).obj N.X)
    (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))) a' b'
  let ψ := Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} x) M.X N.X ≫
    (ProEtale.upperStar Ab.{u + 1} x).map (Mod.tensorObjπ M N)
  ((fibreUnderlying Λ x).inv.app (M ⊗ N)).hom
    ((ψ.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))).hom t)

/-- Tensor comparisons are the canonical maps on pure tensors, equivariant for the
diagonal action; the tensor unit has the trivial representation. The normalization
on generators makes these comparisons natural, associative, unital and symmetric.
Source: blueprint lisse-qlbar-representations, tensor compatibility
(blueprint: thm-lisse-qlbar-representations). -/
def TensorCompatible
    {Λ : Profinite.CondensedRing.{u}} [IsCommMonObj Λ.X]
    {R : Type} [CommRing R] {c : R →+* Γ Λ.X}
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] {x : Spec (.of Ω) ⟶ X}
    {G : Type u} [Group G] {P : ObjectProperty (Modules Λ X)}
    {Q : ObjectProperty (Rep.{u + 1} R G)}
    (C : Correspondence Λ R c x G P Q) : Prop :=
  P (𝟙_ (Modules Λ X)) ∧
  (∀ M N : P.FullSubcategory, P (M.obj ⊗ N.obj)) ∧
  (∀ (M N Z : P.FullSubcategory) (i : M.obj ⊗ N.obj ≅ Z.obj),
    ∃ e : ((C.functor.obj M).V ⊗[R] (C.functor.obj N).V) ≃ₗ[R] (C.functor.obj Z).V,
      (∀ (g : G) (v : (C.functor.obj M).V) (w : (C.functor.obj N).V),
        e (((C.functor.obj M).ρ g v) ⊗ₜ[R] ((C.functor.obj N).ρ g w)) =
          (C.functor.obj Z).ρ g (e (v ⊗ₜ[R] w))) ∧
      ∀ (v : (C.functor.obj M).V) (w : (C.functor.obj N).V),
        (C.comparison.hom.app Z).hom (e (v ⊗ₜ[R] w)) =
          ((fibre Λ x).map i.hom).hom
            (fibreTensor Λ x M.obj N.obj ((C.comparison.hom.app M).hom v)
              ((C.comparison.hom.app N).hom w))) ∧
  ∀ (Z : P.FullSubcategory) (_i : 𝟙_ (Modules Λ X) ≅ Z.obj),
    ∃ e : R ≃ₗ[R] (C.functor.obj Z).V,
      ∀ (g : G) (r : R), (C.functor.obj Z).ρ g (e r) = e r

variable (ell : ℕ) [Fact ell.Prime]

/-- The existing continuous condensed integral ring for a finite subextension.
Source: blueprint lisse-qlbar-representations, clause (1)
(blueprint: thm-lisse-qlbar-representations). -/
abbrev integers (E : PadicAlgCl.FiniteIntermediateField ell) :
    Profinite.CondensedRing.{u} :=
  Mon.mk (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers ell E))

/-- The actual integral-to-rational inclusion on condensed rings.
Source: blueprint lisse-qlbar-representations, lattice convention
(blueprint: thm-lisse-qlbar-representations). -/
def integerInclusion (E : PadicAlgCl.FiniteIntermediateField ell) :
    (integers ell E).X ⟶ Profinite.continuousMapRingObj.{u} E :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap
      (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val)

/-- The inclusion is a map of the existing ring objects.
Source: blueprint lisse-qlbar-representations, lattice convention
(blueprint: thm-lisse-qlbar-representations). -/
instance integerInclusion_isMonHom (E : PadicAlgCl.FiniteIntermediateField ell) :
    IsMonHom (integerInclusion.{u} ell E) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMap
      (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val)

/-- Lattices are embedded lisse integral modules with their specified localization map.
Source: blueprint lisse-qlbar-representations, integrality convention
(blueprint: thm-lisse-qlbar-representations). -/
def HasLattice (E : PadicAlgCl.FiniteIntermediateField ell) (X : Scheme.{u})
    (L : Modules (Mon.mk (Profinite.continuousMapRingObj E)) X) : Prop :=
  ∃ N : Modules (integers ell E) X, IsLisseCoefficientModule (integers ell E).X N ∧
    ∃ i : N ⟶ (Mod.comap (coefficientMap (integerInclusion ell E) X)).obj L,
      Mono i ∧ IsIso (((Mod.extendRestrictAdjunction
        (coefficientMap (integerInclusion ell E) X)).homEquiv N L).symm i)

/-- The rational source is the full subcategory of integral lisse modules, without a
chosen lattice. Source: blueprint lisse-qlbar-representations, clause (2)
(blueprint: thm-lisse-qlbar-representations). -/
def IntegralRational (E : PadicAlgCl.FiniteIntermediateField ell) (X : Scheme.{u}) :
    ObjectProperty (Modules (Mon.mk (Profinite.continuousMapRingObj E)) X) :=
  fun L ↦ IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L ∧ HasLattice ell E X L

/-- Integral algebraic-closure coefficients descend from an integral finite-field model.
Source: blueprint lisse-qlbar-representations, clause (3)
(blueprint: thm-lisse-qlbar-representations). -/
def IntegralAlgCl (X : Scheme.{u}) :
    ObjectProperty (Modules (Mon.mk (Profinite.padicAlgClRingObj ell)) X) :=
  fun L ↦ IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) L ∧
    ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (M : Modules (Mon.mk (Profinite.continuousMapRingObj E)) X),
      IntegralRational ell E X M ∧
      Nonempty ((Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ell E) X)).obj M ≅ L)

/-- Finite free integral continuous representations, including rank zero.
Source: blueprint lisse-qlbar-representations, clause (1)
(blueprint: thm-lisse-qlbar-representations). -/
def IntegralRepresentations (E : PadicAlgCl.FiniteIntermediateField ell) (G : ProfiniteGrp.{u}) :
    ObjectProperty (Rep.{u + 1} (Padic.coefficientExtensionIntegers ell E) G) :=
  fun V ↦ Module.Free (Padic.coefficientExtensionIntegers ell E) V.V ∧
    Representation.IsContinuousIntegral ell E G V.V (linearAction V)

/-- Continuous finite-dimensional representations in the valuation topology, stated by
matrix coefficients so no topology on an unbased vector space is chosen.
Source: blueprint lisse-qlbar-representations, clause (5)
(blueprint: thm-lisse-qlbar-representations). -/
def ContinuousAlgCl (G : ProfiniteGrp.{u}) : ObjectProperty (Rep.{u + 1} (PadicAlgCl ell) G) :=
  fun V ↦ FiniteDimensional (PadicAlgCl ell) V.V ∧
    ∀ (f : Module.Dual (PadicAlgCl ell) V.V) (v : V.V), Continuous fun g : G ↦ f (V.ρ g v)

/-- The simultaneous integral/rational/algebraic-closure correspondences, using a product
of the three families so no large dependent structure recursor is generated.
Source: blueprint lisse-qlbar-representations (1)--(3)
(blueprint: thm-lisse-qlbar-representations). -/
abbrev Correspondences {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u}) :=
  (∀ E : PadicAlgCl.FiniteIntermediateField ell,
    Correspondence (integers ell E) (Padic.coefficientExtensionIntegers ell E)
      (continuousConstants _) x G
      (IsLisseCoefficientModule (integers ell E).X) (IntegralRepresentations ell E G)) ×
  (∀ E : PadicAlgCl.FiniteIntermediateField ell,
    Correspondence (Mon.mk (Profinite.continuousMapRingObj E)) E
      (continuousConstants E) x G (IntegralRational ell E X)
      (fun V ↦ Representation.IsContinuousCoefficient ell E G V.V (linearAction V))) ×
  Correspondence (Mon.mk (Profinite.padicAlgClRingObj ell)) (PadicAlgCl ell)
    (Profinite.PadicAlgCl.constRingHom ell) x G (IntegralAlgCl ell X)
    (fun V ↦ ContinuousAlgCl ell G V ∧
      Representation.IsLAdic ell (PadicAlgCl ell) G V.V (linearAction V))

/-- The integral family of the simultaneous correspondence.
Source: blueprint lisse-qlbar-representations (1)
(blueprint: thm-lisse-qlbar-representations). -/
abbrev Correspondences.integral {ell : ℕ} [Fact ell.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x : Spec (.of Ω) ⟶ X} {G : ProfiniteGrp.{u}} (C : Correspondences ell x G) := C.1

/-- The rational family of the simultaneous correspondence.
Source: blueprint lisse-qlbar-representations (2)
(blueprint: thm-lisse-qlbar-representations). -/
abbrev Correspondences.rational {ell : ℕ} [Fact ell.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x : Spec (.of Ω) ⟶ X} {G : ProfiniteGrp.{u}} (C : Correspondences ell x G) := C.2.1

/-- The algebraic-closure correspondence.
Source: blueprint lisse-qlbar-representations (3)
(blueprint: thm-lisse-qlbar-representations). -/
abbrev Correspondences.algCl {ell : ℕ} [Fact ell.Prime]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x : Spec (.of Ω) ⟶ X} {G : ProfiniteGrp.{u}} (C : Correspondences ell x G) := C.2.2

/-- Lisse integral modules, as the full subcategory specified in clause (1).
Source: blueprint lisse-qlbar-representations (1)
(blueprint: thm-lisse-qlbar-representations). -/
abbrev LisseIntegers (E : PadicAlgCl.FiniteIntermediateField ell) (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsLisseCoefficientModule (integers ell E).X (X := X))

/-- Positive coefficient quotients are finite, by the recorded finite-extension theorem.
Source: blueprint lisse-qlbar-representations (1)
(blueprint: thm-lisse-qlbar-representations). -/
instance finitePositiveQuotient (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) :
    Finite (Padic.coefficientExtensionRing ell E (n + 1)) :=
  Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Classical finite reductions, their normalized action, and completeness of the genuine
fibre. Positive exponent n+1 includes the residue field and avoids the zero quotient.
Source: blueprint lisse-qlbar-representations (1)
(blueprint: thm-lisse-qlbar-representations). -/
def IntegralNormalization {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((Scheme.FiniteEtale.fiber x).obj P)]
    (c : Scheme.GaloisLisseFiniteCorrespondence x G)
    (C : Correspondences ell x G) (E : PadicAlgCl.FiniteIntermediateField ell) : Prop :=
  ∃ reduction : ∀ n : ℕ,
    LisseIntegers ell E X ⥤
      Scheme.LisseModuleSheafCategory X
        (ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1))),
  ∃ projection : ∀ n : ℕ,
    ObjectProperty.ι (IsLisseCoefficientModule (integers ell E).X (X := X)) ⋙ Mod.forget _ ⟶
      reduction n ⋙ classicalAb (Padic.coefficientExtensionRing ell E (n + 1)) X,
  ∃ finiteFibre : ∀ n : ℕ,
    FiniteFibreComparison (Padic.coefficientExtensionRing ell E (n + 1)) x,
  ∃ fibreProjection : ∀ (N : LisseIntegers ell E X) (n : ℕ),
    (fibre (integers ell E) x).obj N.obj ⟶
      (forget₂ (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1)))) Ab.{u + 1}).obj
        (ModuleCat.of _ ((c.e _).functor.obj ((reduction n).obj N)).obj.V),
  ∃ transition : ∀ n : ℕ,
    reduction (n + 1) ⋙ classicalAb (Padic.coefficientExtensionRing ell E (n + 2)) X ⟶
      reduction n ⋙ classicalAb (Padic.coefficientExtensionRing ell E (n + 1)) X,
  ∃ completion : ∀ N : LisseIntegers ell E X,
    (Functor.const ℕᵒᵖ).obj ((fibre (integers ell E) x).obj N.obj) ⟶
      Functor.ofOpSequence
        (X := fun n ↦ (pointSections x).obj
          ((reduction n ⋙ classicalAb (Padic.coefficientExtensionRing ell E (n + 1)) X).obj N))
        (fun n ↦ (pointSections x).map ((transition n).app N)),
  (∀ (N : LisseIntegers ell E X) (n : ℕ),
    ∃ h : scalarSheaf (integers ell E) (continuousConstants _) X N.obj
        (Padic.coefficientExtensionUniformizer ell E ^ (n + 1)) ≫
          (projection n).app N = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((projection n).app N) h))) ∧
  (∀ (N : LisseIntegers ell E X) (n : ℕ) (a : Padic.coefficientExtensionIntegers ell E),
    scalarSheaf (integers ell E) (continuousConstants _) X N.obj a ≫
      (projection n).app N = (projection n).app N ≫
        (classicalAb (Padic.coefficientExtensionRing ell E (n + 1)) X).map
          (ObjectProperty.homMk (Sheaf.smulEnd ((reduction n).obj N).obj
            (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E (n + 1)) a))))) ∧
  (∀ (N : LisseIntegers ell E X) (n : ℕ),
    fibreProjection N n = (fibreUnderlying (integers ell E) x).hom.app N.obj ≫
      (pointSections x).map ((projection n).app N) ≫
      (finiteFibre n).iso.hom.app ((reduction n).obj N) ≫
        (forget₂ (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1)))) Ab.{u + 1}).map
          ((c.τ _).inv.app ((reduction n).obj N))) ∧
  (∀ (N : LisseIntegers ell E X) (n : ℕ) (g : G)
      (v : ((C.integral E).functor.obj N).V),
    (fibreProjection N n).hom
      (((C.integral E).comparison.hom.app N).hom (((C.integral E).functor.obj N).ρ g v)) =
    ((c.e _).functor.obj ((reduction n).obj N)).obj.ρ g
      ((fibreProjection N n).hom (((C.integral E).comparison.hom.app N).hom v))) ∧
  (∀ (N : LisseIntegers ell E X) (n : ℕ),
    Function.Surjective (fibreProjection N n).hom ∧
      ∀ v, (fibreProjection N n).hom v = 0 ↔ ∃ w,
        v = fibreScalar (integers ell E) (continuousConstants _) x N.obj
          (Padic.coefficientExtensionUniformizer ell E ^ (n + 1)) w) ∧
  (∀ (N : LisseIntegers ell E X) (n : ℕ),
    (projection (n + 1)).app N ≫ (transition n).app N = (projection n).app N) ∧
  (∀ (N : LisseIntegers ell E X) (n : ℕ),
    (completion N).app (op n) =
      (fibreUnderlying (integers ell E) x).hom.app N.obj ≫
        (pointSections x).map ((projection n).app N)) ∧
  Nonempty (∀ N : LisseIntegers ell E X, IsLimit (Cone.mk _ (completion N)))

/-- Simultaneous tensor and canonical scalar comparisons, including rationalization of
EVERY lattice and scalar extension of EVERY finite-field model.
Source: blueprint lisse-qlbar-representations (2),(3), tensor/scalar paragraph
(blueprint: thm-lisse-qlbar-representations). -/
def Compatibilities {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u}) (C : Correspondences ell x G) : Prop :=
  (∀ E, TensorCompatible (C.integral E)) ∧
  (∀ E, TensorCompatible (C.rational E)) ∧
  (TensorCompatible C.algCl) ∧
  (∀ E, ScalarCompatible (C.integral E) (C.rational E)
    (integerInclusion ell E) (Padic.coefficientExtensionIntegers ell E).subtype) ∧
  (∀ E, ScalarCompatible (C.rational E) C.algCl
    (Profinite.padicSubfieldRingObjToPadicAlgCl ell E) (algebraMap E (PadicAlgCl ell))) ∧
  (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
    ScalarCompatible (C.rational E) (C.rational F)
      (Profinite.padicSubfieldRingObjMap ell h) (IntermediateField.inclusion h).toRingHom)

/-- All five clauses and the fibre convention of the theorem. On a normal scheme the
integral source properties below equal the entire lisse source. Together with
the fields-of-definition conjunct, the fully faithful and essentially surjective correspondence
therefore applies to all lisse modules and all continuous finite-dimensional representations.
The last conjunct gives the same conclusion for regular schemes.
Source: blueprint lisse-qlbar-representations (1)--(5)
(blueprint: thm-lisse-qlbar-representations). -/
def Conclusion {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((Scheme.FiniteEtale.fiber x).obj P)]
    (c : Scheme.GaloisLisseFiniteCorrespondence x G)
    (C : Correspondences ell x G) : Prop :=
  (∀ E, IntegralNormalization ell x G c C E) ∧
  (Compatibilities ell x G C) ∧
  (∀ E, FiniteFreeFibre (integers ell E)
    (Padic.coefficientExtensionIntegers ell E) (continuousConstants _) x) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ell,
    FiniteFreeFibre (Mon.mk (Profinite.continuousMapRingObj E)) E (continuousConstants E) x) ∧
  (FiniteFreeFibre (Mon.mk (Profinite.padicAlgClRingObj ell)) (PadicAlgCl ell)
    (Profinite.PadicAlgCl.constRingHom ell) x) ∧
  ((∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z)) →
    ∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (L : Modules (Mon.mk (Profinite.continuousMapRingObj E)) X),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L → HasLattice ell E X L) ∧
  ((∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z)) →
    ∀ L : Modules (Mon.mk (Profinite.padicAlgClRingObj ell)) X,
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) L → IntegralAlgCl ell X L) ∧
  (∀ V : Rep.{u + 1} (PadicAlgCl ell) G,
    ContinuousAlgCl ell G V →
      Representation.IsLAdic ell (PadicAlgCl ell) G V.V (linearAction V)) ∧
  (IsRegularScheme X →
    ∀ z : X, IsDomain (X.presheaf.stalk z) ∧ IsIntegrallyClosed (X.presheaf.stalk z))
```

## New

The exact declarations in the Old block are now in
`Sheaf.Paper.LisseQlbarRepresentationDefs`, verbatim. The item re-exports them with:

```lean
public import Sheaf.Paper.LisseQlbarRepresentationDefs
```

No definition or statement has a different elaborated meaning. The theorem itself keeps
its exact signature. The new definition node records ownership of the extracted data.

## Users

`python3 tools/downstream.py Sheaf.Paper.LisseQlbarRepresentations --uses
AlgebraicGeometry.ProEtale.LisseRepresentation` reported zero downstream importers;
the only namespace occurrence was the item itself. A direct search of both Lean roots
confirmed there are no external consumers to adapt.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseQlbarRepresentations | K3 | Public re-export; same theorem signature and data. |
| Sheaf.Paper.NormalizedLisseCoefficientCorrespondences | K3, new | Imports the data to state clauses (1)--(3). |
| Sheaf.Paper.LisseGeometricFibresFiniteFree | K3, new | Imports the data to state the fibre calculation. |
| Sheaf.Paper.NormalLisseFiniteCoefficientLattice | K3, new | Imports the data to state normal lattice existence. |

No target statement is changed. The definitions used to interpret targets are unchanged.

## Status

landed 20261026T023429-L-565479 2026-10-26 (merge of deliver/K3/Sheaf.Paper.LisseQlbarRepresentations)
