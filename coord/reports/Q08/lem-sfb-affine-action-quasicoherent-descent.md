## Worker report

This delivery states lem-sfb-affine-action-quasicoherent-descent without proving it. The
main module is Sheaf.AlgebraicGeometry.AffineActionQuasicoherentDescent. Its declarations
jointly render the clauses of the node; the principal declaration is
AlgebraicGeometry.affine_action_quasicoherent_descent. Every theorem has proof `by sorry`.
All definitions have actual data; the two choices are taken from uniqueness theorems
fixing the scalar-extension coaction on every pure tensor and the atlas comparison arrow
on its underlying torsor-space and base maps. No arbitrary action, quotient, comparison,
structural morphism or identification is an input replacing a canonical construction.

Hypotheses and clauses, read against the node:

- A field k is `(k : Type u) [Field k]`. The group scheme is `(G : Scheme.{u})`
  with `G.Over (Spec (.of k))`, `GrpObj (G.asOver ...)`, and `IsAffine G`.
  The geometric conclusions bind `Smooth (G ↘ Spec (.of k))`,
  `LocallyOfFiniteType ...` and `QuasiCompact ...`. Over the affine base `Spec k`,
  `IsAffine G` is equivalent to affineness of its structure morphism. The two
  finite-type predicates are the recorded meaning of finite type, with no condition on D.
- H is literally `Γ(G, ⊤)`. The canonical Hopf instance is the already landed
  `HopfAction.coordinateHopfAlgebra`; its multiplication, counit and inversion
  are the coordinate maps of the given group scheme. The added already-existing
  definition dependency def-sfb-affine-coordinate-hopf-algebra owns that interface.
- D is any commutative k-algebra, and rho is the existing
  `HopfAction.AlgebraCoaction k Γ(G, ⊤) D`. Its `map`, `counit` and `coassoc`
  are exactly the given k-algebra map and the two equations; no private copy is made.
- The map j:A→D is encoded by `[Algebra k A] [Algebra A D] [IsScalarTower k A D]`.
  Specifying this compatible algebra structure is equivalent to specifying the node's
  k-algebra map j. Its invariant-image hypothesis is `hA : ∀ a, ρ.map
  (algebraMap A D a) = algebraMap A D a ⊗ₜ[k] 1`.
- `coactionLeftMap` is the actual Spec map of `(S tensor 1) swap rho`, using
  `G.isoSpec` and Mathlib's `pullbackSpecIso` for the canonical affine product
  comparison. `coactionLeftArrow_laws` states the identity and associativity laws;
  `coactionLeftAction` contains this map and those named proof obligations.
- `coactionQuotient` is `SchemeAction.torsorGroupoid` with this exact action.
  This is the SAME torsor total category used by `affineActionQuotientStack`.
  The latter wrapper requires `[Algebra.FiniteType k E]`, so the wrapper cannot
  be applied to arbitrary D; its underlying recorded general construction is used
  directly, without copying its objects, arrows, actions, total category or pullbacks.
  `coactionAtlas` and `coactionAtlasObject` reuse `quotientAtlas` and `trivialObject`.
  `coactionQuotient_isFibred` states the cartesian lifting law needed by the recorded
  algebra-sheaf definition, using the imported torsor fibre-product formulas.
- `affine_action_quotient_structure` states algebraicity and existence of psi with
  its actual atlas normalization `ModuliTwoIso (coactionAtlas.comp ψ)
  (discreteModuliMap (yoneda.map coactionBaseArrow))`, followed by the recorded
  `IsQuasiCompactAlgebraicModuliMap` and `IsQuasiSeparatedAlgebraicModuliMap`.
  The qc predicate's additional test universes remain independent `v,w`.
- For every arbitrary `[CommRing C] [Algebra A C]`,
  `coactionScalarExtension_existsUnique` states the generator formula
  `(d tensor_A c) ↦ sum ((d_i tensor_A c) tensor_k h_i)` for EVERY finite
  presentation `rho(d)=sum d_i tensor h_i`. Empty sums are included. The resulting
  `coactionScalarExtension` has both coaction laws as part of `AlgebraCoaction`.
- `affine_action_quotient_baseChange` states a based equivalence between the ACTUAL
  `moduliTwoFiberProduct` of psi and `Spec C` and the torsor quotient of `D tensor_A C`.
  The normalization preserves torsor space, action, projection and total-arrow
  space map, and fixes the D and C components of its equivariant map. Thus it is
  the lift/forget-lift equivalence in the node, not an arbitrary category equivalence.
  The k-algebra structure on C with its scalar-tower law is its unique induced one;
  it is explicit to keep the actual Spec C map well typed, not an extra restriction.
- `CoactionQuotientAlgebras` is the full subcategory of the recorded
  `ModuliAlgebraSheaf` satisfying its recorded `IsQuasicoherentModuliAlgebra`.
  It uses the original big fppf total site and sheaf/module definitions. Atlas
  rings have the common existing universe u+1; B is allowed in u+1 as well,
  so no smallness or finite-generation condition on an algebra is imposed.
- `affine_action_quasicoherent_descent` gives an equivalence to the new category
  `HopfAction.EquivariantAffineAlgebra`. Its objects are exactly the node's B,
  structure map and extending coaction; its morphisms are equivariant D-algebra maps.
  The natural ring equivalence `e M` identifies its algebra with actual atlas sections,
  and fixes the structure map via `coactionAtlasUnit`.
- `IsAtlasCoaction` fixes the coaction as the actual descent transport. The helpers
  `coactionRightSource`, `coactionRightTarget`, `coactionRightTransport` and the two
  projection arrows use `trivialTorsorFunctor` on the action groupoid: the right
  arrow parameter is the inverse LEFT-action label. The predicate equates its
  sheaf restriction with the given finite coaction expansion, multiplying by
  actual pullbacks of regular functions on G. This precludes twisting the coaction
  while retaining only an equivalence of underlying algebra categories.
- The main theorem identifies ALL morphisms under `e`, and states
  `IsSurjectiveModuliAlgebra f.hom ↔ Function.Surjective (F.functor.map f).map`.
  The former is local sheaf surjectivity on the big fppf site, exactly as recorded;
  no left-exactness assertion is substituted.
- The ring equivalence `gamma M` identifies the recorded
  `moduliGlobalSectionsRing M.obj.right` with the actual equalizer subring
  `(F.functor.obj M).invariants`. Its evaluation formula is
  `e M (gamma M b).val = b.val (op coactionAtlasObject)`. The final clause states
  naturality for every algebra map, as equality of the underlying invariant elements.
- `coactionChange` is literal postcomposition of each torsor's equivariant map;
  its space, action, projection and total-arrow maps remain the original ones.
  `IsCoactionRestriction` specifies the original precomposition restriction of
  the ring sheaf AND its algebra structure. `coactionRestriction_exists` supplies it.
- `coactionRestriction_scalarExtension` identifies restricted atlas sections with
  `B tensor_D E`, normalized by `b ↦ b tensor 1` and `a ↦ 1 tensor a`; its last
  clause gives restriction of every compatible global section by that same formula.
  Apply it with D replaced by D_C and E by D_C tensor_C Cprime. Canonical tensor
  associativity identifies this with D tensor_A Cprime and gives the node's further
  scalar extension. The comparison is fixed on algebra and scalar generators,
  so its naturality in algebra homomorphisms and repeated restrictions is built
  into literal sheaf precomposition and the uniquely normalized tensor isomorphism.
  This does NOT assert invariants commute with tensor product.
- `affine_action_structure_sections` is the B=D case, an actual ring isomorphism
  between structure global sections and `RingHom.eqLocus rho.map includeLeft`,
  normalized by the Gamma-Spec atlas evaluation. `coactionBaseSections` is the
  pointwise pullback of functions by psi on every object. Its formula is real data,
  with its named compatibility theorem. `affine_action_structure_baseMap` identifies
  that map under atlas evaluation with `algebraMap A D`. At D_C over C this is
  exactly `includeRight`, hence c maps to 1 tensor c.
- There is no `Algebra.FiniteType` hypothesis on D, C, E, or B anywhere. The
  scalar-extension restriction and structure-section formulas require no flatness.

Dependency declarations read and used:

- Mathlib Field (Algebra.Field.Defs), `CategoryTheory.GrpObj`
  (CategoryTheory.Monoidal.Grp), `Smooth` (AlgebraicGeometry.Morphisms.Smooth),
  `LocallyOfFiniteType` and `QuasiCompact` (FiniteType and QuasiCompact), `Spec`
  and `Spec.map` (Scheme), `TensorProduct` (LinearAlgebra.TensorProduct.Defs),
  and `Limits.pullback` (Limits.Shapes.Pullback.HasPullback).
- Sheaf.AlgebraicGeometry.AffineActionQuotientStack: `affineActionScheme`,
  `affineActionQuotientStack` and all its general `SchemeAction` torsor/atlas data.
  The actual total category, trivial torsor and action arrows come from its public
  SchemeActionTorsorGroupoids dependency. The wrapper finite-type binder was checked.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `IsAlgebraicModuliStack`.
- Sheaf.AlgebraicGeometry.StackQcqsMorphism: `IsQuasiCompactAlgebraicModuliMap`,
  `IsQuasiSeparatedAlgebraicModuliMap`, with the latter's actual relative diagonal.
- Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra: `ModuliAlgebraSheaf`,
  `IsQuasicoherentModuliAlgebra`, `IsSurjectiveModuliAlgebra`,
  `moduliStructureSheaf`, `moduliStructurePresheaf`, `moduliGlobalSectionsRing`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `IsFibredInGroupoids`,
  `moduliTwoFiberProduct`, `ModuliTwoIso`, `discreteModuli`, `discreteModuliMap`.
- Sheaf.RingTheory.HopfActionModuleData: `HopfAction.AlgebraCoaction`, its exact
  `Counital` and `Coassociative` predicates. Sheaf.AlgebraicGeometry.HopfCoactionLinearization:
  `HopfAction.coordinateHopfAlgebra` (canonical Mathlib coordinate Hopf structure).
- Mathlib's `HopfAlgebra.antipodeAlgHom`, tensor algebra map/commutation, `G.isoSpec`
  and `pullbackSpecIso` provide real coordinate data. `ObjectProperty.FullSubcategory`
  provides the quasi-coherent algebra category.

The recorded proof modules already available are imported without `public`:
ActionGroupoidTorsorComparison, StackChartwiseSmoothEtaleCalculus, the affine tilde
adjunction, affine tensor comparison, and tensor-pullback affine sections. The currently
unrecorded smooth-groupoid quotient, module descent/tensor/cokernel, qcqs atlas/diagonal,
representable locality and fibre-product proof prerequisites are not invented or assumed
as extra hypotheses. Their steps are retained explicitly in the theorem docstrings.

Edge cases checked before and during writing: D=0, C=0 and B=0 (no nontriviality
assumptions); trivial group; nonreduced arbitrary algebras; infinitely generated D/C/B;
empty tensor expansions; arbitrary characteristic; nonflat scalar extension; morphisms
between all the corresponding algebras, including identity maps and successive base
extensions. No finite-type conclusion for D is used. The coaction left-action law was
checked against g acting as x times g inverse, including noncommutative groups. The
right-arrow transport uses the inverse left label, so the displayed coaction is rho,
not rho followed by antipode. Global sections are compatible families, not evaluation
at a nonexistent terminal object of the quotient. No STATEMENT-DISPUTED or node fault.

Searches made before writing:

- msearch leanfinder: "Quasi coherent algebras on an affine quotient stack are
  equivariant algebras and global sections are invariants": eight affine Gamma,
  module/sheaf and quasi-coherence results, no matching statement.
- msearch loogle: "HopfAction.AlgebraCoaction, AlgebraCoaction, Comodule": no hits;
  the Mathlib-indexed service does not know the project's coaction namespace.
- msearch grep: "AlgebraCoaction|equivariant.*[Aa]lgebra|[Aa]lgebra.*[Cc]oaction":
  only an unrelated Lie-subalgebra restriction result in Mathlib.
- msearch leansearch: "Equivariant commutative algebras with a Hopf algebra coaction
  form a category": HopfAlgCat, CoalgCat and CommBialgCat results, not coactions of
  a fixed Hopf algebra on arbitrary commutative algebras.
- rg in lean/WeilConjectures for coactions/equivariant algebra, and the item id:
  finite torsor algebra descent exists, not this arbitrary affine quotient statement.
- rg in lean/Sheaf found the existing HopfAction algebra coaction, the finite-type
  AffineActionStackPresentation and FlatAffineActionStackPresentation, neither
  an equivalence of arbitrary algebra categories; these signatures were read.
- DAG grep found Hopf-action module data and many consumers; blueprint_refs.py
  search "equivariant algebra" found 0 blueprint nodes. The ancestor command
  returns None, consistent with the item's inherited null ancestor.
- The upstream name index contains scheme quasi-coherent algebras, no category of
  arbitrary equivariant affine algebras. It was also searched for the new names.

Source texts read: stacks-sheaves.tex proposition-quasi-coherent (06WT),
groupoids.tex definition-equivariant-module (03LF), plus the recorded quotient,
qcqs and algebra-sheaf module docstrings and complete declarations. The withdrawn
CompactObject example was followed to its recorded upstream replacement and read.

## New nodes

`def-sfb-equivariant-affine-algebra` defines precisely the missing category of
commutative algebras extending an existing Hopf algebra coaction, its equivariant
algebra morphisms and its equalizer invariant subring. Its source is the algebra-object
form of Stacks 03LF and 06WT. It reuses `HopfAction.AlgebraCoaction`, not a duplicate
of that notion. The three search kinds and the DAG/upstream/project searches are
recorded verbatim in its `mathlib_searches`. The category laws are actual composition
of algebra maps. Its `invariants` is `RingHom.eqLocus`. There are no theorem stubs in
this definition module. The item cites this new node plus the already landed Hopf
coaction and canonical affine coordinate-Hopf definition nodes.

## Second reading by Q08

Author's second pass, not an independent review; independent review is the maintainer's
as required by the dispatcher brief. Reopened the node and each delivered declaration.
Checked the left-action conversion and inverse parameter on right-arrow transport;
the normalized algebra equivalence retains both unit and coaction, ALL morphisms,
local-surjection equivalence, and the ring/naturality of invariant sections. Checked
that the base-change comparison fixes both coordinate projections and preserves
actual torsor actions, and that sections use the literal quotient site. Caught and
fixed a missing explicit scalar-ring universe view in the restriction formula and
added actual base-function pullback, so the c↦1 tensor c clause is a Lean formula.
No change to the node statement, proof, proof dependencies or hypotheses was needed.
The scalar-extension coaction and atlas arrow choices each have unique generator
characterizations. Checked every definition for real data and every theorem for a
sorry-only body. The new category has no private copies of the existing coaction.
