## Worker report

The module `Sheaf.Paper.DivisibleTorsionSupportedInjectiveModels` states
`AlgebraicGeometry.Etale.DivisibleTorsion.supported_injective_models`, with `sorry` as
its entire proof. The node's statement is unchanged. Supporting definitions describe the
actual kernel presentations, maps, supported complexes, section complexes and normalized
comparisons in the same module; there is no new independent mathematical notion requiring
a new DAG node. Every definition has real data. The existence of the coefficient-valued
kernel presentations is part of the theorem's conclusion, and the kernel universal property
fixes these presentations up to their unique inclusion-preserving isomorphism.

Hypotheses and objects, matched individually:

* Noetherian schemes X and Z: `{Z X : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]`.
* Closed immersion: `(i : Z ⟶ X) [IsClosedImmersion i]`. The complementary open is the
  dependency's canonical `(closedSupportOpenComplement i).ι`; a separately named isomorphic
  complement is unnecessary data. This is exactly X minus the closed image.
* Ordinary small-etale module categories: `Mod X l r = Sheaf X.smallEtaleTopology
  (ModuleCat.{u+1} (A l r))`; `Ab X` uses `AddCommGrpCat.{u+1}` on that same site.
* Prime ell: `(l : ℕ) [Fact l.Prime]`. Divisible sheaf: `(M : Ab X) [Epi (l • 𝟙 M)]`.
  This is a sheaf epimorphism, not the stronger assertion of surjectivity on all sections.
* Any injective resolution, with the specified lower bound: `(I : CochainComplex.Plus
  (Ab X)) [I.obj.IsStrictlyGE 0]`, `_hI : ∀ q : ℤ, Injective (I.obj.X q)`, augmentation
  `a : single (Ab X) M ⟶ I`, and `_ha : QuasiIso a.hom`. `single` is the actual single
  complex in degree zero. This integer-indexed interface includes every resolution in the
  node, rather than replacing it by a chosen resolution. Mathlib's recorded
  `InjectiveResolution` uses natural indices; the four explicit conditions above render
  its injectivity and quasi-isomorphism content on the node's given integer complex.
* Positive r, a, b: `ℕ+`, avoiding irrelevant exponent-zero cases without excluding r=1.
  `A l r` is `ULift (ZMod (l ^ (r : ℕ)))`, the standard size lift to coefficient universe u+1.
* `F_r`: `(T.layer r).functor.obj M`. Each `Layer` includes a natural inclusion into the
  original abelian sheaf, its vanishing composite with l^r, and `IsLimit` of that kernel
  fork. Thus it is precisely the ordinary torsion kernel with its canonical A_r action.
* `J_r`: `J (T.layer r) I`, the actual termwise kernel functor on I, with induced differential.
* `K_r`: `K i (T.layer r) I`, applying the published `closedUpperShriek`, namely inverse
  image of the kernel of the open adjunction unit.
* `E_r`: `E i (T.layer r) I`, applying `sections Z l r` termwise; sections are evaluation
  at `op (Scheme.Etale.mk (𝟙 Z))`, the terminal small-etale object.

Conclusions, matched individually:

* The augmentation is the kernel augmentation: `augmentation` is the termwise kernel
  functor applied to a, preceded by `HomologicalComplex.singleMapHomologicalComplex`.
  Its `QuasiIso` conclusion and injectivity of every term of J assert exactly that this
  is an injective resolution over A_r.
* Every K term is injective over A_r: the third conjunct of the first universal r clause.
* The actual derived comparison in D-plus is the isomorphism family `c r`. Its source
  is localization `Q` of K, its target is the recorded `closedSupportPlus` applied to F
  in degree zero. The first normalization equation identifies its composite with the
  derived augmentation with the published `rightDerivedFunctorPlusUnit` at J. This fixes
  the map, not merely the existence of isomorphic derived objects.
* For every nonnegative m, `CocycleComparison` supplies the additive isomorphism from
  the actual module-category homology of E to derived Hom from the constant rank-one
  sheaf into the shift of the target. The degree-zero source is localized `single` of
  `unitSheaf`, canonically the dependency's constant coefficient complex.
* The phrase sending one to a cocycle is formalized by `evalOne`, using
  `constantSheafAdj ... (Scheme.Etale.isTerminalMkId Z)` and evaluation at 1, and the
  equation for every abstract cycle z and sheaf Hom cocycle chi with that evaluation.
  `cocycleMap` is constructed from the HomComplex cohomology class, the localization
  functor and its canonical shift comparisons, followed by c. Thus the additive
  equivalence is constrained on every cocycle representative, not an arbitrary equivalence.
* The three degreewise short exact rows use `row`, `supportRow`, and `sectionRow` and
  their `ShortExact` conclusions. In abelian complex categories, `ShortExact` is
  equivalent to degreewise short exactness. Their maps are literally the `map` of the
  normalized inclusion and reduction natural transformations.
* Outer scalars of the first two rows are restricted to A_(a+b): `Jr`, and `Kr` after
  applying support in that common ring. Their coefficient map is the actual
  `quotient l h`, the canonical ZMod cast homomorphism lifted through ULift.
* For N >= r the inclusion and reduction are fixed by `Layers.incl_normalization`
  and `Layers.red_normalization` after their kernel inclusions: respectively identity
  on the original sheaf and multiplication by `l ^ ((N : ℕ) - (r : ℕ))`.
  Applying the actual functors to these maps fixes the corresponding J, K and E maps.
  For N=a+b and target b the reduction exponent is (a+b)-b=a, as required.
* The common-ring comparison is `d N r h` with its own derived-unit equation at `Jr`.
  `SupportRestriction.iso` identifies restriction of the actual supported complex with
  support of the restricted complex. Its `counit` field fixes this isomorphism by the
  underived adjunction counit; `supportComplexIso` applies it termwise.
* The equation involving `mapDerivedCategoryPlusFactorsh`, `supportComplexIso`, `d`,
  `c`, `coefficientMate` and `sourceRestrictionIso` identifies the restriction of c with
  the common-ring comparison. `coefficientMate` is explicitly the unit/counit formula
  for the mate of the inverse ordinary direct-image restriction comparison, using
  `closedSupportPlusAdjunction` and `closedSupportPlusCounit`. This fixes the derived
  counit normalization, including N=r; it cannot be an unnormalized chosen isomorphism.
* The universal f naturality equation for d includes all inclusions, reductions and
  their composites in any common coefficient ring; the next equation records composition
  of the actual chain maps. Kernel inclusions are monic by `Layer.isKernel`, so their
  normalization also forces the usual inclusion/reduction identities and composites.
  The functorial section construction and the cocycle equation give the same E maps.
* The coefficient-sheaf row is `row T (single (Ab X) M) ...`, with its `ShortExact`
  proof hF. Its three objects are the canonical single-complex images of F_a,
  F_(a+b), F_b. `RowComparison` uses the three augmentation maps and canonical
  derived-unit normalization to identify the K row with its derived supported row.
  Both ordinary arrows and the connecting arrow have explicit equations, using
  `connecting` from `DerivedCategory.triangleOfSESδ` and the fixed right-adjoint
  shift structure `closedSupportPlusCommShift`. Thus the whole coefficient triangle,
  and not only its first two arrows, agrees with the derived supported image.

Statement dependencies read and used:

* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public coefficient
  imports: ordinary `Sheaf ... (ModuleCat ...)`, `DerivedCategory`, `DerivedCategory.Plus`.
* `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective`, the full fields of `CategoryTheory.InjectiveResolution`.
  Its explicit integer-complex rendering above avoids an unnecessary dependency repair.
* `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`:
  `AlgebraicGeometry.Etale.supportedKernel`, `supportedClosedInverseImage`. Its source
  identifies these with the already published arbitrary-coefficient
  `sectionsWithSupport` and `closedUpperShriek`; the module-valued latter is used.
* `Sheaf.AlgebraicGeometry.ClosedSupportPlusAdjunction`:
  `closedSupportOpenComplement`, `closedSupportPlus`, `closedSupportPlusAdjunction`,
  `closedSupportPlusCounit`, `closedSupportPlusCommShift`.

All recorded proof-dependency modules are imported, with proof-only imports nonpublic.
The theorem docstring contains the node's nine-step proof, including simultaneous
cohomological dimension shifting for restricted torsion terms and the cone argument
for the connecting arrow. No statement correction or dependency-node repair was needed.

Sources read: Stacks `sites-cohomology.tex`, `lemma-torsion` (0DD7), first paragraph;
`etale-cohomology.tex`, the full supported-sheaf definition, `lemma-sections-with-support-acyclic`
(09XQ), its proof and the following derived-functor paragraph. The latest blueprint ancestor's
proof was read; the node itself expressly supplies an agent-derived finite-layer refinement,
not a claim that 0DD7 already states every finite-layer clause. The designated example
`CompactObject.lean` is now withdrawn and contains no declarations; the delivered module uses
the current public module header and expose convention of the actual dependency modules.

Edge cases checked: M=0; X or Z empty; Z=X (empty complementary open); r=1;
a=b=1; N=r; equal successive coefficient indices; characteristic ell, which is not excluded
because these are arbitrary ordinary etale sheaves, not a purity assertion. Strict vanishing
below zero is imposed on the given resolution only, as the node says. Coefficients and
sections live in u+1, with no equation imposed between site object and morphism universes.
The displayed constructions make sense in all of these cases, and the elementary divisible
abelian-group row gives precisely the required surjection even on global supported sections.

Searches actually run:

* `msearch.py ... leanfinder "Torsion kernels of divisible abelian sheaf injective resolution
  compute supported finite coefficient cohomology"`: 8 hits, including `Sheaf.H`,
  `InjectiveResolution.extEquivCohomologyClass_extMk` and K-injective infrastructure;
  none states the supported finite-layer coefficient-compatible theorem.
* `msearch.py ... loogle "Sheaf, InjectiveResolution"`: 0 hits with unknown identifier
  `Sheaf`; this unsuccessful query is not evidence of absence.
* `msearch.py ... grep "torsion.*[Kk]ernel|[Kk]ernel.*torsion" CategoryTheory`: 0 hits.
* `rg` of WeilConjectures and Sheaf for torsion kernels, divisible injectives and the item
  id: the id has no upstream hit. Existing `SheafCohomologyTorsion` proves divisibility
  and acyclicity of finite torsion kernels but not this theorem. `TorsionInjectiveSubcomplex`
  concerns the union of all torsion, not fixed finite torsion layers. Existing scalar
  restriction and direct-image comparison declarations are reused instead of duplicated.
* Source reads searched Mathlib's `Algebra.Module.ZMod`, homology, constant-sheaf,
  single-complex, right-derived-plus and short-exact-triangle APIs. The new helpers
  are presentations or maps belonging to this one statement, not replacements for
  those existing notions.

Validation: the full module passed `scompile.py` in both sandbox and final module namespaces,
with no errors or warnings. Only the main theorem has a postponed proof.

## Second reading by Q43

I reread the actual node and final signature after compiling. This is a second pass by the
same worker, not an independent-agent review: the dispatcher explicitly forbids starting
another agent, and independent review belongs to the maintainer for this delivery.

The reread checked the prime and sheaf-epimorphism hypotheses, the arbitrary integer-indexed
resolution and its degree-zero augmentation, the actual kernel inclusions and power maps,
three strict rows, finite-ring restriction, cocycle evaluation at one, fixed derived unit,
closed counit mate, and connecting-arrow equality against the clauses listed above.
An earlier draft had only an unconstrained additive cocycle equivalence; it was replaced
by `evalOne`/`cocycleMap` and the representative normalization equation. An earlier draft
recorded only strict rows; `RowComparison` now also includes the derived connecting arrow.
The final comparison families include both the fixed-ring and arbitrary common-ring forms,
with their explicit compatibility equation. No hypothesis was added to obtain the scalar
comparison and no finite coefficient restriction was assumed flat.
