## Worker report

The module states `CategoryTheory.CondensedBar.condensed_product_bar_resolution_model`.
Its sole postponed proof is that theorem. The structure `ProductResolutionModel`
records the clauses, with genuine data in all auxiliary definitions. No statement
correction, new independent notion, or dependency-record repair is made. The item
adds the already-landed `def-sfb-condensed-equivariant-bar-data` to `stmt_deps`
(brief-stage2 §5: statement dependencies may gain landed nodes), since its
`InternalFunctions` and `BarDiagram` interfaces occur in the signature.

Source read: the complete node and seven proof steps, and the current blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). The latter gives the direct-image context; the node is explicitly an
agent-formulated internal-bar input, not a claim that this paragraph itself contains
these bar formulas. Its source's ordinary condensed-module reference remains WANTED;
the local generic ingredients are the free/internal-Hom adjunction, Stacks 070J for
bounded-below injectives, 070K/070Y for derived-unit comparisons, and the first-quadrant
augmentation comparison already recorded in the proof-dependency modules.

Hypotheses and clauses, in order:

* A commutative condensed ring: `A : CondensedBar.Ring.{u}`, the existing `CommMon`
  of abelian sheaves on `coherentTopology Profinite.{u}`. Its `A.toMon` is the recorded
  arbitrary `Profinite.CondensedRing`, with the existing `ringComm` instance. This adds
  no presentation by a topological ring. `Modules A` is exactly `CategoryTheory.Mod`
  of this internal ring, not discrete modules over its global sections.
* Profinite G and H: `Type u`, group, topology, topological-group, compact, Hausdorff,
  and totally disconnected instances, exactly as the existing action interface.
  The site uses profinite objects in u, values in u+1, and category objects/derived
  categories in u+2. `HasDerivedCategory.{u+2}` is the recorded size convention,
  not an identification of site object and morphism universes.
* Actions and inflation: `Equivariant A (G × H)` is the recorded `ActionModule` with
  all continuous generalized elements acting linearly and naturally on restrictions.
  `V : Invariants A (G × H)` is the existing normalized invariant functor with its
  inclusion, fixed-after-every-base-change image condition and inflation adjunction.
  `F : InternalFunctions A` is the existing specification of actual internal Hom
  from free represented modules, including its `internalHom` natural isomorphism.
  These are choices of the objects the prose already uses, not flatness, exactness,
  injective-preservation, projectivity, or bar-exactness hypotheses.
* A specified nonnegative equivariant resolution: the conclusion quantifies over
  every `N` and `I : InjectiveResolution N`; its `cocomplex`, `injective`, `ι`, and
  `quasiIso` fields give exactly N[0] to I. The same I occurs in every column and total.
* C^(a,b,q): `B.onComplex I.cocomplex` uses the existing additive `ProductBar`
  coefficient functor. `columnIso` identifies its (a,b)-coefficient functor with
  `forgetAction ⋙ F.functor (productParameter G H a b)`. `column_evaluate` fixes
  this identification on all test objects and all base changes via `productGraph`.
* All cofaces/codegeneracies: the existing `ProductBar` fields `faceG`, `faceH`,
  `degeneracyG`, `degeneracyH` prescribe the first action face, adjacent products,
  final deletion, and inserted identity on sections. Its doubly cosimplicial functor
  imposes the identities and mixed commutation. `ProductBar.additive` and degreewise
  application to I impose commutation with each resolution differential.
* D and T: the existing `B.diagonalDouble`, `B.diagonalTotal`, `B.iteratedDouble`,
  and `B.iteratedTotal` are finite-diagonal nonnegative totals. Their definitions
  use alternating cofaces and the existing total functor, with precisely
  delta_diag + (-1)^n d_q and delta_G + (-1)^a delta_H + (-1)^(a+b) d_q.
  T is a defined construction in the node, not a further quasi-isomorphism assertion.
* Free-product identification: `freeProduct` is for arbitrary profinite P,Q,
  including empty ones; `freeProduct_generator` fixes [(p,q)] to [p] tensor [q]
  on every profinite base change, using the existing actual adjunction generators.
  This characterization also forces naturality in P,Q.
* Currying: `curryIso P Q` is natural in the coefficient module. `curry_evaluate`
  fixes its evaluation at every two-stage base change to c(p,q). Thus it is the
  closed-adjunction isomorphism, including parameter naturality, rather than a bare
  existence of an unnormalized isomorphism. `columnIso` with this gives the displayed
  iterated internal Hom for every a,b,q.
* Simultaneous derived columns: `column_unit` is the canonical second-variable
  derived-unit isomorphism on UI. `internalColumn` identifies R internal Hom applied
  to UN[0] with the actual column on I. `internalColumn_normalization` specifies its
  composite with the recorded internal-Hom identification and derived unit as R of
  the forgotten resolution augmentation. `resolvedColumn` and its normalization
  give the equivariant coefficient-functor version. `operator_compatibility` uses
  `barDerivedOperator` for every pair of simplex maps, including the two first
  faces and every degeneracy. This states compatibility of a single resolved
  diagram, not independently chosen representatives.
* Product diagonal: `singleBar : BarDiagram (G := G × H) F` has the recorded
  single-group formulas. `diagonalIso` is an isomorphism of full cosimplicial
  diagrams, and `diagonal_evaluate` specifies tuple-of-pairs to pair-of-tuples
  coordinate reordering on every generalized section, including degree zero.
* J and j_D: `augmentation` has source the degreewise invariants of I and target
  `B.diagonalTotal I.cocomplex`. `augmentation_f` is exactly invariant inclusion,
  the represented empty-parameter augmentation, and the (0,q) total coprojection.
  `augmentation_quasiIso` asserts this actual map is a quasi-isomorphism.
* Q(D) ≅ Q(J) ≅ R Gamma(N[0]): Q is the existing `productBarQ`, extension by zero
  followed by the ordinary derived localization. The first iso is the inverse of
  localization of `augmentation`. `derivedIso` gives R Gamma to Q(J), and
  `derived_normalization` fixes it using the derived unit and the given resolution
  map. Its inverse has the direction displayed in the prose.

Dependencies read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
* `Sheaf.CategoryTheory.CondensedProductActionInflation`,
  `Profinite.CondensedAction.product_action_inflation` (through its existing
  action-category instances; no new abelian structure is copied).
* `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
* `def-weil-size-convention` is the explicit convention record, not a declaration.
* `Sheaf.CategoryTheory.CondensedInternalBarResolution`,
  `Profinite.CondensedAction.InternalBar.freeAdjunction` and `pureTensor`;
  `CondensedBar.freeParameter` is its existing represented specialization.
* `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`,
  `SheafOfModules.tensorClosed`; the already recorded `InternalFunctions.internalHom`
  retains internal modules and the internal-to-sectionwise comparison.
* `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `CategoryTheory.Injective`;
  the actual resolution structure is Mathlib's `InjectiveResolution`.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its normalized unit.
* `WeilConjectures.CategoryTheory.DoubleComplexTotal`,
  `HomologicalComplex₂.firstFiltration` and the underlying Mathlib total constructions.
* Proof declarations already stated: `CondensedBar.Assertion` and its data interfaces
  in `CondensedEquivariantBarData`, `Mod.nonempty_equalizerInternalHomAdjunction`,
  `CochainComplex.isKInjective_of_injective`,
  `CondensedBar.nonempty_injectiveRows`, and
  `CondensedBar.condensed_bar_total_augmentation` with its `barRightDerived`,
  `barUnitAt` and `barDerivedOperator` helpers. The first four are available through
  the listed imports; the equalizer interface has its explicit proof import.
* The proof-only nodes `lem-sfb-condensed-free-linearization-tensor` and
  `lem-sfb-condensed-action-injective-restriction` have no recorded module in this
  snapshot, so there is no such module to import. They are not assumed as extra
  hypotheses: their uses are postponed in the sole theorem proof.

One-definition check: reused `ProductBar`, its test-section/operator formulas,
`productBarParameters`, all existing total constructions, `productBarQ`, and
`productBarResolutionIso` from `Sheaf.CategoryTheory.CondensedProductBarComparison`.
That module also contains the downstream theorem, which is NEVER used here. Its
proof-import back to this item must be omitted to prevent an import cycle, as
per stages/2-statements.md §3(7). This import uses definitions and action-category
instances based only on `product_action_inflation`, not the downstream theorem's
sorry. No private copy of this already existing notion is introduced.

Searches made:

* msearch leanfinder, query “A single equivariant injective resolution models a
  product internal bicosimplicial bar and diagonal derived invariants”: eight hits,
  primarily `Rep.barResolution`, `Rep.standardResolution`, and ordinary injective
  resolutions. Their signatures use ordinary rings and abstract group representations,
  not internal modules for condensed group actions, so none states this node.
* msearch loogle, query `MonoidalClosed.curryIso`: zero hits; unknown identifier.
  Direct Mathlib source search found `MonoidalClosed.ihomCurryIso`, the generic
  currying component, not the compatible condensed-group resolution theorem.
* msearch grep, `(bicosimplicial|condensed.*bar|bar.*condensed)`: zero Mathlib hits.
* msearch leansearch, “Internal Hom free modules profinite products currying bar
  injective resolution”: eight hits, including `InjectiveResolution` and
  `LightCondensed.ihomPoints`. The latter is for light condensed modules over an
  ordinary coefficient ring, so does not cover arbitrary internal condensed rings.
* rg in live `lean/WeilConjectures` and `lean/Sheaf` for bicosimplicial/product bar,
  the item ID, and `ProductBarResolutionModel`: found the downstream product-bar
  definitions and generic single-group model, no theorem with this exact statement.
  Also inspected Mathlib's internal-currying and injective-resolution source, and
  upstream internal-module Hom/tensor and derived-category signatures.
* DAG concept search for product bar/model found this node and its comparison and
  normalization siblings, not a missing independent notion to duplicate.

Edge cases: Fin 0 tuples are retained; no positivity or nontrivial-group assumption
is imposed. Trivial factors retain all unnormalized nerve degrees and degeneracies.
N=0 is quantified with EVERY injective resolution, not only the zero resolution.
The zero condensed ring is allowed. Arbitrary freeProduct P,Q includes empty sets.
All group/resolution indices are nonnegative and each total diagonal is finite;
no exactness of infinite products, free-module projectivity, or global expression
of arbitrary sheafified sections as sums of generators is assumed.

## Second reading by Q44

The dispatcher explicitly forbids other agents, so this is a separate second pass
by the same worker, not an independent reviewer. I reopened the complete node,
ProductBar's existing fields and the new signatures. The first draft gave only
invertibility of the derived units; I added actual normalized `internalColumn` and
`resolvedColumn` comparisons and all-simplex `operator_compatibility` so the
compatible-derived-diagram clause is explicit. I also checked the orientation of
the two factors in currying (apply H-Hom first, then G-Hom), the tuple-pair direction
in `diagonal_evaluate`, and the (0,q) augmentation. No source statement is changed.
The maintainer supplies the independent review specified by the dispatch brief.

Validation: scompile.py completed both sandbox and final-module compilations
with exit code 0 and no errors or warnings. The wrapper reported 88.7 seconds and
792.7 seconds including server slot waits; its per-file Lean limit was unchanged.
deliver2.py --no-push returned OK: commit 278c87ffb21 passes the preflight
and compiles; nothing pushed.
