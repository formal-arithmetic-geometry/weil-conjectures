## Worker report

The delivery states `CategoryTheory.flat_groupoid_quotient_open_presentation` in
`Sheaf.AlgebraicGeometry.FlatGroupoidQuotientOpenPresentation`. Its proof is `sorry`.
The two data definitions `quotientOpenScheme` and `quotientOpenInclusion` are the actual
open subscheme, its structural composite, and its inclusion. Neither uses postponed data.

The quotient is specified by the already landed `SchemeGroupoidQuotientPresentation`:
`Q`, `p`, and `P` are a presentation of the fppf stackification up to based equivalence,
including the original arrow identification, composition, and local object lifts. This
is the same interface used by the landed finite-flat-affine-groupoid consumer, and is
not an arbitrary algebraic stack or an arbitrary map in place of the quotient. Algebraicity
is a conclusion. No finite-inertia, separation, finite-type, smoothness, quasi-compactness,
or Deligne--Mumford assumption is imposed.

Hypotheses and clauses, in node order:

- The field is `(k : Type u) [Field k]`. Schemes are `U R : Over (Spec (.of k))`;
  `s t : R ⟶ U` are maps over this field. `universe u v w` and
  `BasedCategory.{v,w}` explicitly bind the scheme, stack morphism, and object sizes.
  The metatheoretic size convention has no declaration to import.
- The scheme-groupoid operations are `e`, `i`, `c`, with
  `hG : IsGroupoidScheme s.left t.left e i c`; composition uses `pullback s.left t.left`,
  with the later arrow first. The quotient-presentation record additionally retains
  its equivalent recorded `Scheme.IsGroupoid` laws and the composition identification.
- Flatness and local finite presentation of BOTH source and target are the four
  explicit instances on `s.left` and `t.left`.
- `IsAlgebraicModuliStack Q` is exactly algebraicity. The next four conjuncts give
  representability by spaces, surjectivity by field-extension lifts, and flatness and
  local finite presentation on every etale scheme chart of every scheme base change.
- The canonical `R ≃ U ×_Q U` is the `IsEquivalence` of the actual
  `moduliTwoFiberLift` from `h_R`, built from `h_s`, `h_t`, and precisely `P.arrows`.
  Its projections are these two functors by construction, so the identification
  retains both s and t and their comparison, not just an unrelated equivalence.
- When both maps are finite, `ModuliSchemeTest @IsFinite p` says that every scheme
  base change of p is a finite SCHEME morphism. The next scheme-test property is
  `LocallyOfFinitePresentation ∧ QuasiCompact ∧ QuasiSeparated`, finite presentation.
  Finiteness is deliberately not tested on arbitrary etale SOURCE charts.
- `b : OpenModuliSubstack Q ≃ {V : U.left.Opens // s.left ⁻¹ᵁ V = t.left ⁻¹ᵁ V}`
  is the asserted bijection. `W₁.IsContainedIn W₂ ↔ (b W₁).val ≤ (b W₂).val`
  expresses the inclusion correspondence in both directions.
- For each W the displayed equivalence `a` and `IsSchemeModuliBaseChange a ...`
  identify `U ×_Q W` with the ACTUAL open scheme `(b W).val`, over U with its inclusion.
- `R_V` is the actual open scheme `s.left ⁻¹ᵁ (b W).val`; b's subtype records its
  equality with the t inverse image. The maps `sV,tV,eV,iV,cV` have compatibility
  equations with the original inclusions and original operations. Thus the
  `Nonempty (SchemeGroupoidQuotientPresentation ... W.category q)` identifies
  W with `[V/R_V]`, with the original restricted operations. The displayed two-isomorphism
  identifies q followed by the inclusion with p restricted to V.
- The two `IsPullback` clauses are exactly the source and target base-change squares.
  If the original maps are finite locally free, the last implication gives
  `sV.left.IsFiniteLocallyFree ∧ tV.left.IsFiniteLocallyFree`.
- `Function.Surjective (moduliSchemePointMap p)` is the final point-lifting assertion
  for the existing field-object quotient `ModuliPoints Q`.

The opening inertia, properness and separatedness sentences fix surrounding terminology;
they impose no hypothesis and have no extra conclusion in this lemma. They are not turned
into additional restrictions on Q.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, and the
  scheme-test definition `IsRepresentableWith` underlying the chart interfaces.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory`,
  `discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`:
  `SchemeGroupoidQuotientPresentation` and its `arrows`, full-faithfulness,
  fppf stack, local-surjectivity and composition fields. Its record was landed before
  this delivery. Added its definition node to stmt_deps; no dependency record changed.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`, `category`,
  `IsContainedIn`, `fullModuliInclusion`; its landed definition node is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `moduliTwoFiberLift`,
  `IsSchemeModuliBaseChange`; its landed definition node is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`,
  `ModuliSchemeTest`; its landed definition node is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`: `IsSurjectiveModuliMap`,
  owned by landed definition node `def-sfb-surjective-moduli-map`, added to stmt_deps.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`: `moduliSchemePointMap`,
  owned by landed definition node `def-sfb-stack-point-topological-space`, added to
  stmt_deps. The existing theorem dependency `lem-sfb-stack-point-topology` is retained.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`, read in full;
  it supplies a pseudofunctor local-description theorem, whereas the already landed
  scheme-presentation definition directly supplies the total-category interface needed here.
- Mathlib `Algebra/Field/Defs.lean:180`: `Field`; `Morphisms/Flat.lean:42`: `Flat`;
  `Morphisms/FinitePresentation.lean:45`: `LocallyOfFinitePresentation`;
  `Morphisms/Etale.lean:41`: `Etale`; `Morphisms/Proper.lean:42`: `IsProper`;
  `Morphisms/Finite.lean:39`: `IsFinite`; `Sites/Fpqc.lean:40–54`:
  `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`. Their full definitions were read.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:895`:
  `Scheme.Hom.IsFiniteLocallyFree`, exactly finite + flat + locally finitely presented.

Stated proof dependencies are imported, including the space point/open calculus,
flat-lfp openness and scheme finiteness/affine permanence modules. The following proof
nodes have no recorded Lean module on the read base, so have no import to add:
`lem-sfb-flat-groupoid-algebraic-quotient`, `lem-sfb-space-finite-fppf-descent`,
`lem-sfb-invariant-open-substack-descent`, `lem-sfb-representable-stack-point-surjectivity`,
and `lem-sfb-fppf-groupoid-stack-presentations`. They are proof prerequisites, not missing
notions needed to type this statement. The docstring retains all eight proof steps and
names these dependencies for stage 3.

Edge cases checked before writing: empty U and R, the empty invariant open, the whole
open, the identity groupoid R=U, nonfree stabilizers (in particular a finite flat
non-smooth group in positive characteristic), variable finite-locally-free rank,
and non-quasi-compact schemes. The statement never assumes a constant rank, rational
point lifts over k, finiteness of the relation in the first clause, or an etale atlas U.
Point lifting permits residue fields and common extensions through ModuliPoints.
The ambient Q universes v,w are independent of u; no artificial equality is introduced.

Searches actually performed (2026-10-24):

- msearch LeanFinder: `Flat locally finitely presented groupoid quotient algebraic stack
  invariant open substack correspondence`: eight hits, scheme flat/open/lfp results;
  none states this stack theorem.
- msearch Loogle: `"quotientStack"`: zero hits.
- msearch grep: `quotientStack|quotient_stack|flat.groupoid|invariant.open.*stack`: zero hits.
- msearch LeanSearch: `flat groupoid algebraic stack quotient invariant open substacks`:
  eight hits on scheme flatness/open immersions and unrelated group quotients, no match.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for `quotientStack`, `quotient.stack`,
  `groupoidStack`, `invariantOpen`, `OpenSubstack`, `FlatGroupoid`: found action quotients,
  the existing open-substack notion, `SpaceGroupoidQuotientPresentation` and, through
  the DAG search, the exact scheme presentation interface. Read those modules, reused
  the scheme interface; no general theorem with the present combined conclusions exists.
- grep of the item id in `lean/WeilConjectures`: no match.
- rg for the three proposed declaration names across Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no match.

Sources read: Stacks criteria.tex, `lemma-flat-quotient-flat-presentation` and
`theorem-flat-groupoid-gives-algebraic-stack` (06FH, 06FI), including their proofs;
stacks-properties.tex `lemma-substacks-presentation` (0507), including its proof.
The node's smooth-atlas descent argument correctly extends 0507's smooth-presentation
wording to this fppf presentation. No statement correction is needed.

## Second reading by Q31

A second pass was performed by the assigned worker, with the node and completed module
open; no separate agent was started, as the dispatch brief expressly forbids that.
I checked the four instances on s and t separately, the retained groupoid composition
orientation, and that Q is NOT assumed algebraic. The canonical relation comparison
uses P's actual arrow two-isomorphism and both specified endpoint maps. The finite
clause uses scheme base changes, not chartwise finiteness. The open bijection records
invariance as equality of scheme opens, not merely an implication on points; its
pullback equivalence fixes the projection to U. The restricted groupoid has all five
operations, their compatibility equations, the quotient presentation with its atlas
comparison, and BOTH pullback squares. Finally the finite-locally-free implication
and the actual point-map surjectivity are separate clauses. The first compile caught
a sort error: a data-carrying restricted presentation was used as a proposition;
it is now correctly wrapped in Nonempty. No mathematical weakening was made.

## Repair of returned head 3b5022216443

H2: added both existing definition owners to the item statement dependencies:
`def-sfb-surjective-moduli-map` owns `CategoryTheory.IsSurjectiveModuliMap` in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`;
`def-sfb-stack-point-topological-space` owns `CategoryTheory.moduliSchemePointMap`
in `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`. Read each current node
record and the full defining signature and docstring. Both are landed existing:true
records. Retained `lem-sfb-stack-point-topology` exactly as requested.

The Lean file is byte-identical to the returned delivery, SHA256
`bafcd41ba48521b697a7b024783c4993c201e63af00fc9a2a905cc362ab3e655`.
The item was compared with the current read-only main node: its only field changes
are `lean` and the six added, already landed statement dependencies. The delivery
wrapper rebases the repaired delta onto current main. No dependency node is edited.
The second reading of this repair checked both declaration-owner bindings against
their source modules, the retained topology theorem edge, and the unchanged signature.
