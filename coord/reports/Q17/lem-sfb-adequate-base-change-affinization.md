## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateBaseChangeAffinization` states
`CategoryTheory.adequate_base_change_affinization` with its proof `sorry`.
The two transparent abbreviations `adequateBaseChangeCategory` and
`adequateBaseChangeProjection` use the existing actual 2-fibre product and its
second projection; their data are complete. They belong to the construction in
this node, rather than introducing an independent notion. No node statement,
statement dependency, proof or proof dependency was changed; only `lean` was set.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`.
- The algebraic stack over k is `F : BasedCategory.{v, w} (Over (Spec (.of k)))`
  with `hF : IsAlgebraicModuliStack F`. Both total-category universes are independent.
- The two algebraic spaces over k are `Y T : AlgebraicSpace (Spec (.of k))`.
  Their morphisms are the existing full-subcategory morphisms, i.e. sheaf maps.
- The morphism phi is `φ : BasedFunctor F (discreteModuli Y.obj.obj)` and
  `hφ : IsAdequateModuliSpace F hF Y φ` is exactly its recorded adequate-moduli
  predicate, including qcqs, canonical structure-sheaf isomorphism, and local
  power lifting for all quasi-coherent algebras on every affine etale base change.
- The map g is an unrestricted `g : T ⟶ Y`. There is no flatness, finite-type,
  Noetherian, separated-diagonal, DM, or other additional binder.
- X_T is `adequateBaseChangeCategory φ g`, definitionally the existing
  `moduliTwoFiberProduct φ (discreteModuliMap g.hom.hom)`. Its projection f is
  `adequateBaseChangeProjection φ g`. The existential `hFT` records the
  algebraicity of this same construction and is a conclusion, not a hypothesis.
- B = f_* O is expressed by `B : T.QCAlg` and a ring equivalence `e W` from
  its ring on every etale chart W to the value of the existing
  `moduliDirectImage hFT.1.1 T f (moduliStructureSheaf X_T hFT.1.1)`.
  The first conjunct says these equivalences commute with every restriction.
  The second says they send the algebra structure map to exactly
  `moduliStructureMapApp`, which pulls back each regular function to all scheme
  objects. Thus this is the actual direct-image algebra, including operations,
  restrictions and structural map, rather than an unspecified algebra on T.
  Membership in QCAlg supplies precisely quasi-coherence of its underlying module.
- The coefficient transport is necessary because the recorded stack direct image
  takes values in `CommRingCat.{max (u+1) v w}`, while the recorded relative-Spec
  interface uses `CommRingCat.{u}`. The natural ring equivalences express the
  same algebra in the latter universe. Qcqs descent on a scheme atlas gives
  smallness of sections. No equation between universes or extra assumption is used.
- `C : RelativeSpecData T`, with `C.HasChartFormula`, is the existing normalized
  relative-Spec anti-equivalence. H is `(C.relativeSpec B).obj.left`, and h is
  `(C.relativeSpec B).obj.hom`. The result of `relativeSpec` is an `AffineOver T`,
  whose property already says that every scheme test is affine and representable.
  The counit identifies its direct-image algebra with B, so h is the morphism
  defined by the structural map, as required.
- The factorization is `a : BasedFunctor X_T (discreteModuli H.obj.obj)` and
  `Nonempty (ModuliTwoIso (a.comp (discreteModuliMap h.hom.hom)) f)`. Equality is
  represented by the canonical notion of 2-isomorphism over Sch/k. Its target
  is a discrete fibred groupoid of an algebraic space, so this is the stated
  equality of space-valued maps, with no lost automorphism data in the source.
- The next conjunct is `IsAdequateModuliSpace X_T hFT H a`, exactly adequacy of a.
- Canonicity is retained by the last equation. For a T-chart W, a compatible
  H-chart q, a comma object i over W, and a comma object r for a over q, an arrow
  b from i's source to r's source gives a scheme map to q. When its composite
  to W is i's structural map, evaluating `e W s` at i equals the pullback along
  that scheme map of s through `C.counitAlgebra` and the recorded direct-image
  projection. This says exactly that a pulls each section of f_* O back to its
  own evaluation. Etale lifts of H-charts cover every scheme object, so this
  characterizes the canonical map locally and hence globally. It does not
  permit a different endomorphism of B. The outer ULift.up is the existing
  canonical regular-function coefficient lift.
- Universal homeomorphism is the quantified `∀ (T' : AlgebraicSpace (Spec (.of k)))
  (t : T' ⟶ T), IsHomeomorph ...`. The function is the actual second projection
  of the 2-fibre product of the discrete maps h and t on `ModuliPoints`.
  Both topologies are the recorded `moduliSmoothPointTopology`. For algebraic
  spaces, their discrete fibred groupoids give exactly the point spaces of the
  node, and the 2-fibre product presents H times_T T'. All space maps are tested.

Dependency interfaces read and used:

- `Field` in Mathlib/Algebra/Field/Defs.lean (the field Mathlib match).
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace`, full definition and docstring.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, its full-subcategory definition, representability
  and etale predicates and small etale site.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliStructureSheaf`, `moduliDirectImage`, `moduliDirectImagePresheaf`,
  `ModuliPushforwardIndex`, `moduliStructureMapApp`, `moduliChartSchemeMap`, and
  their full signatures and section/pullback docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence`:
  `RelativeSpecData`, `relativeSpec`, `counitAlgebra`, `StructureAlgebraModel.projection`,
  `HasChartFormula`, and the statement `space_relative_spec_correspondence`.
  Its public algebra and module interfaces supply `QCAlg` and `ModuleChart`.
- `Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets`:
  `moduliSmoothPointTopology` and the full statement of
  `smooth_presentation_closed_subsets`, with the existing point quotient and maps.
- Existing inherited helpers `moduliTwoFiberProduct`, `ModuliTwoIso`,
  `discreteModuliMap`, and `moduliTwoFiberSnd` are reused, not copied.

Proof imports additionally include the recorded modules for
`lem-a1-space-affine-etale-cover`, `lem-trf-space-fibre-products-etale-covers`,
`lem-weil-pbc-morphism-into-affine-scheme` (Mathlib GammaSpecAdjunction), and
`lem-pur-all-element-powers-spectrum-homeomorphism` (Mathlib Prime/Homeomorph).
The algebraic-stack definition is already publicly imported by the statement
interfaces. Remaining proof-dependency nodes have no Lean or Mathlib record yet;
they are named in the complete natural-language proof docstring and have no
invented imports. Every one of the node's eight proof steps is represented there.

Searches made on 2026-10-24:

- msearch LeanFinder: "An arbitrary base change of an adequate moduli space factors
  canonically through its relative spectrum with an adequate moduli map and universal
  homeomorphism". Eight hits, including `pullbackSpecIso_hom_base_assoc`,
  `of_pullback_fst_Spec_of_codescendsAlong`, and affine-space base-change formulas;
  none states this algebraic-stack result.
- msearch Loogle: "IsAdequateModuliSpace, RelativeSpecData". Zero hits, unknown
  identifier IsAdequateModuliSpace in the Mathlib service.
- msearch grep, Mathlib AlgebraicGeometry:
  `adequateModuli|adequate_moduli|adequate.*affinization`. Zero hits.
- msearch LeanSearch: "adequate moduli space arbitrary base change canonical
  affinization universal homeomorphism". Eight hits about scheme affine morphisms
  and universally closed scheme maps, no adequate-moduli factorization.
- rg on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `adequateModuli|adequate_moduli|adequate.*affinization|IsAdequateModuliSpace`.
  Only the already-recorded adequate-moduli definition matched; no existing theorem.
- rg for this exact node id in `lean/WeilConjectures`: no match.
- Additional rg for relativeSpec and affinization found the recorded space
  relative-Spec interface and scheme-only affinization lemmas, which do not state
  the stack theorem. No duplicate definition or missing independent notion was found.

Source checked: published primary PDF
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf, printed p.509,
Proposition 5.2.9(3) and its proof. It explicitly uses arbitrary base change and
relative Spec of the direct-image structure algebra. Definition 3.3.1 supplies
its universal-homeomorphism consequence. The node deliberately asks only for
that topological consequence, not all adequate-homeomorphism properties.

Edge cases checked before writing: identity g (the direct-image algebra is O and
h is the identity up to the recorded counit); empty T and the empty stack over
empty Y (the zero algebra and empty relative Spec are allowed, no Nonempty or
nonzero-algebra condition); non-flat g and characteristic p (no flatness binder,
and h is only a universal homeomorphism, never asserted to be an isomorphism);
nontrivial nilpotent algebras (canonicity equation rules out an arbitrary algebra
endomorphism); arbitrary total-category universes v,w (transport by ring
isomorphisms, no forced equality with u); identity and arbitrary subsequent t
are both included in the universal quantifier. No statement dispute or node fault.

Validation: the prescribed scompile.py compiled the module separately as sandbox
and library mode, in 4.7 s and 4.5 s respectively. Both passed with no warnings
or errors. Only the displayed theorem has a sorry; definitions are actual data.

## Second reading by Q17

The dispatcher explicitly requires one worker and prohibits other agents. This
section records a separate second pass by the same worker; the maintainer will
perform the independent delivery review. I reopened the node and compiled file
and checked the field, base, stack, spaces, phi and g binders; the actual 2-base
change and second projection; the direct-image equivalences with restriction
and structure compatibility; QCAlg membership; the affine relative-Spec object;
the factorization 2-isomorphism; adequacy of a; the evaluation normalization;
and every T' and t in the homeomorphism clause. No mismatch was found. In
particular `hFT` and the coefficient equivalences are conclusions, not hidden
hypotheses, and affineness is part of the type of `C.relativeSpec B`. The final
normalization is necessary: factorization and adequacy alone would not pin down
the canonical map in the presence of nilpotents. No change was needed after
this reading. This is not claimed to be an independent second worker's review.
