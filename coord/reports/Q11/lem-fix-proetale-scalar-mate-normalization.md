## Worker report

The module `lean/Sheaf/Paper/ProEtaleScalarMateNormalization.lean` states
`AlgebraicGeometry.ProEtale.proEtaleScalarMateNormalization`. It identifies the
restriction of the existing canonical coefficient mate with the counit-defined
projection arrow, and states the unreduced B-linear counit equation. All three
theorem proofs are `sorry`; definitions contain real constructions only. The item
node changes only in `lean`. No statement correction or independent new notion
is needed.

Source read: `literature/stacks-project/sites-cohomology.tex`, Tag 0B56,
`equation-projection-formula-map`, lines 13657–13680. This defines the projection
arrow as the adjunct of the pullback tensor comparison followed by the geometric
counit tensor identity, without assumptions. The node's five proof steps are
included in the main theorem's docstring. Its implicit canonical scalar/tensor
identification is supplied with its complete normalization, rather than assumed.

Hypotheses and clauses:

* The finite commutative rings are `{A B : Type u} [CommRing A] [CommRing B]
  [Finite A] [Finite B]`. The ring map is `(φ : A →+* B)`.
* An arbitrary scheme morphism is `{T V : Scheme.{u}} (f : T ⟶ V)`.
  There is no properness, flatness, immersion or other geometric hypothesis.
* Ordinary unbounded categories are the existing `Scheme.proEtaleDerivedCategory`.
  `(M : Scheme.proEtaleDerivedCategory T A)` is unrestricted. The actual site
  remains `Scheme.ProEt`, with objects in universe u+1 and morphisms in u.
* `S_W` is the existing `directImageScalarExtension φ W`, namely
  `Scheme.proEtaleRingDerivedExtension (Scheme.proEtaleConstantRingMap φ)`.
  `U_W` is `(scalarMateRestriction φ W).mapDerivedCategory`, the exact
  termwise descent of the recorded `proEtaleRingRestrictScalars`.
* The scalar adjunction is the existing representative-normalized
  `proEtaleRingDerivedExtensionAdjunction`, used by the published pullback
  comparison. This is retained, with its universal scalar derived counit used
  explicitly in `IsScalarMateDerivedTensor`.
* The canonical lambda is `directImageScalarPullbackIso φ f`. The chi in the
  statement is exactly the published `directImageScalarComparison φ f`, whose
  definition uses `CategoryTheory.mateEquiv` with the actual geometric adjunctions.
  Neither is supplied as an arbitrary argument.
* The canonical `h_W : U_WS_W ≅ - ⊗ B_W` is
  `scalarMateDerivedTensorIso φ W aW`. Its defining theorem asserts uniqueness
  subject to `IsScalarMateDerivedTensor`. The ordinary precursor is uniquely
  normalized on EVERY local section b tensor m, sending it to m tensor b under
  the actual module sheafification unit. Thus the B-last convention is explicit.
  Its chain comparison is `scalarMateOrdinaryComplexIso`.
* The derived normalization quantifies over flat-term K-flat P and Q and EVERY
  quasi-isomorphism q from Q to B_W[0]. Its equation compares the given tensor
  model's representative map, q, h, the original scalar derived counit and the
  exact restriction factorization with the localization of the actual ordinary
  tensor comparison. This both fixes h uniquely and permits nonflat B.
* The parameters `aV` and `aT : Scheme.ProEtaleTensorModel ...` present the
  chosen derived tensors by the recorded signed total tensor on flat K-flat
  representatives. They are the choice of model for the tensor already mentioned
  in the node; no property of φ, f or M is assumed. The result holds for every
  such model, so there is no arbitrary tensor comparison hypothesis.
* The canonical direct-image identification d is `scalarMateRestrictionPush`.
  It specializes `proEtaleRingRestrictionDerivedDirectImage` using the actual
  constant-ring maps and their proven naturality square. No preservation of
  K-injectives by restriction is assumed.
* The coefficient v is `scalarMateDerivedCoefficientPullback φ f`. It is built
  from the actual ordinary restriction/pullback comparison, the uniquely
  unit-normalized B-unit pullback of `proEtaleProjectionUnit_existsUnique`,
  exact pullback factorization, and the canonical single-complex comparison.
* The first conjunct is h_V inverse, U_V(chi), d, and Ru_*^A(h_T), equal to
  `CategoryTheory.derivedProjectionFormulaMate` for the actual A-geometric
  adjunction and `proEtaleCanonicalTensorComparison`, followed by Ru_*^A of
  identity tensor v. This is precisely the node's identification with its
  specified projection arrow, including the coefficient pullback identification.
* The second conjunct reads L_B(chi) followed by epsilon_B equals lambda
  followed by S_T(epsilon_A), with the same objects as the displayed counit
  equation in the node. Lean composes arrows from left to right.
* Naturality is encoded by natural isomorphisms h, lambda and d, the existing
  natural transformation chi, and the existing bifunctor tensor comparison.
  The component equality is quantified over arbitrary M. There is no boundedness
  or flatness assumption on the coefficient map or on the complexes.

Dependencies inspected and used (recorded modules are imported):

* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, through `proEtaleRingRestrictScalars`.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv` and
  its counit convention, through the existing chi definition.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and its ordinary finite
  coefficient framework; the item's specified constant-ring presentation uses
  the published `proEtaleDerivedCategory`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback`, the constant-section coefficient
  identification and ordinary module adjunction.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`, the universal K-flat scalar model
  already underlying the published operations.
* `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, including its
  representative scalar unit and counit normalization.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  The already published concrete small-site specialization is
  `Scheme.proEtaleCanonicalTensorComparison` in
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`. We reuse its normalized comparison
  and `ProEtaleTensorModel`, preserving the original site universes.
* `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`.
  Its specified arrow is the existing `CategoryTheory.derivedProjectionFormulaMate`
  from `Sheaf.Paper.ProjectionFormulaArrows`, using the actual geometric adjunction.
* `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `Scheme.proEtaleRingRestrictionDerivedDirectImage`,
  `proEtaleRingRestrictionPullbackInv`, its named invertibility theorem, and
  `proEtaleRingSheafChangeAdjunction`.
* `Sheaf.SecSmoothPurity.DirectImageScalarOperations`: the existing
  `directImageScalarExtension`, `directImageConstantPush`,
  `directImageConstantAdjunction`, `directImageScalarPullbackIso`, and
  `directImageScalarComparison`. Only the operations module is imported;
  the later scalar-exchange theorem is not imported.
* `Sheaf.Paper.ProEtaleProjectionFormulaArrows`:
  `Scheme.proEtaleProjectionUnit_existsUnique`, retaining its unique normalization.
  The proof dependency modules for K-flat resolutions, ordinary sheaf tensor,
  module pullback tensor, tensor descent, K-flat complexes, total complexes and
  the constant-ring inverse image are also imported, without public where needed
  only by the postponed proof.

The auxiliary definitions and two auxiliary existence/uniqueness statements
are the canonical identifications explicitly asserted in steps 1 and 3 of THIS
node, listed in its `lean.declarations`. They are not new independent notions
or arbitrary Nonempty choices. `Classical.choose` is used only with uniqueness
and full normalizations. Ordinary tensor, scalar extension, restriction,
module sheafification, derived categories and all geometric functors are reused.

Edge cases checked before drafting: zero rings and zero modules are allowed;
zero and unbounded M are not excluded; identity maps and empty schemes have the
same normalized maps. A nonflat example Z/4 → Z/2 is allowed: B[0] is resolved
by Q and need not itself be K-flat. No lower bound, upper bound, Tor amplitude
or inverse-image universe equality is added. No hypotheses quantify over a
smaller universe than the actual coefficient sheaves. Both normalizations are
nonvacuous, since ordinary pure tensors generate after sheafification and the
recorded K-flat resolution theorem supplies the P,Q representatives.

Searches actually run on this resumption:

* msearch leanfinder: "The derived scalar extension direct image mate on the
  pro-etale site restricts to the canonical tensor projection morphism";
  eight hits, including ordinary ModuleCat scalar adjunction formulas and
  SheafOfModules.pullbackObjUnitToUnit, but no exact derived pro-etale normalization.
* msearch loogle: "CategoryTheory.mateEquiv, SheafOfModules.restrictScalars";
  zero hits.
* msearch grep: "derived.*[Ss]calar|[Ss]calar.*derived|projectionFormula";
  one unrelated Mathlib submonoid comment.
* Project rg for scalarMate/ScalarMate and scalar/projection combinations in
  `lean/Sheaf` and `lean/WeilConjectures` found the etale scalar-mate projection
  theorem, which has a different site and coefficient encoding, and the existing
  ordinary pro-etale operations reused here. No exact statement of this node.
* Read `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison` and its
  `exists_changeOfRings_tensor_comparison`. Its site object/Hom universes are
  both u and its existence conclusion does not fix the pure-tensor map. It
  cannot instantiate the current small site or select the required h. The
  helper here supplies precisely this node's normalized constant-ring comparison
  on the unchanged small site, using actual sheafification and tensor operations.

The earlier retained report described missing published artifacts. On resumption
the prescribed initial dry run correctly diagnosed the absent node copy. The
minimal probe subsequently compiled, then the full import closure and statement
compiled. Compiler diagnostics in our draft were repaired (explicit tensor
universes, integer rather than natural complex indices, explicit use of a named
invertibility theorem, and one line-width issue). No launcher files, live
sources, compiler limits or global build were modified.

## Second reading by Q11

The dispatcher expressly forbids starting other agents; this is the worker's
second reading, not an assertion of independent review. The maintainer supplies
independent review after delivery.

Reread the node, Stacks' counit definition and the final file together. The finite
ring binders and arbitrary scheme-map/object binders match. The first equality
has the source tensor with B last and all four h/d conjugations in the correct
direction; its right side uses the existing projection mate and canonical
coefficient v, rather than defining the projection to be chi. The second equality
is B-linear before restriction and has the exact mate-counit order. The actual
scalar/pullback comparisons, direct images, and adjunctions are reused. The
helper h has a uniqueness characterization on all flat K-flat resolutions of
B[0], with the original scalar counit, so the nonflat case is retained. The
ordinary normalization uses arbitrary local b rather than just 1; this prevents
an unspecified scalar/tensor automorphism. All supporting definitions have real
data, every theorem has only sorry, and each declaration has source and blueprint
docstrings. No change to the informal statement was made.

## Returned-timeout self-check, 2026-10-21

The prescribed first dry run of the retained packet passed preflight and per-file
compilation (dry-run commit 9f007e42f95). The independent explicit scompile.py
check then compiled both sandbox and library module forms cleanly in 46.0 s and
45.9 s, respectively, within the unchanged 60 s limit. Thus the returned timeout
at c9154b16100b did not reproduce. Following the dispatcher's saved-packet
instruction, retain the Lean source rather than change the mathematical interface
without a current diagnostic. Delivery tooling rebases the packet onto current live
state; comparison with the read clone confirms that only the item's lean field
changes. No definition, hypothesis, normalization or conclusion was changed.

For the required final reading, checked the source's counit-defined projection
arrow and the current dependency interfaces against the saved module. The two
conjuncts still express the restricted mate/projection identification and the
unrestricted B-linear counit equation. The arbitrary tensor models retain the
specified representative normalization, and the nonflat coefficient is resolved
rather than assumed flat. The node's lean.statement matches the complete theorem
signature verbatim; all lines meet the 100-character limit, all variables and
universes are explicit, and exactly the three named theorem proofs are sorry.
