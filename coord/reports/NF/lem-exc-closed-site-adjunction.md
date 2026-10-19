## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction` states
`AlgebraicGeometry.Scheme.AffineProEt.exists_closedSiteAdjunction`, with proof `sorry`.
It introduces no definitions or new nodes, and changes only the item's `lean` field.

Hypothesis and clause correspondence:
- `A : Type u`, `[CommRing A]`, and `I : Ideal A` bind precisely the affine closed
  immersion Spec(A/I) → Spec A of the referenced definition. No field, nonzero,
  finiteness, proper-ideal, or nilpotence hypothesis is imposed.
- The node's functor v is the existing `closedSiteLift A I`; its functor u is the
  existing `closedSiteBaseChange A I`. These are exactly the functors of
  `def-exc-closed-site-lift`, including their actual maps, not abstract replacement functors.
- “v is left adjoint to u” is the witness
  `adj : closedSiteLift A I ⊣ closedSiteBaseChange A I`. Mathlib's `Adjunction`
  includes the natural unit/counit and both triangle identities.
- “uv canonically the identity” is `IsIso adj.unit`. The unit has source the
  identity on the closed-site basis and target `closedSiteLift A I ⋙
  closedSiteBaseChange A I`; its inverse identifies this composite with the identity.
  This ties the identification to the same adjunction, rather than asserting an
  unrelated natural isomorphism or literal equality of chosen pullbacks.

Dependency declarations read and used:
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `AlgebraicGeometry.Scheme.AffineProEt.closedSiteLift` and `closedSiteBaseChange`.
  Read the full module, including coordinates, object, map and functor definitions.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction` and its `unit`.
- Proof imports: `Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction`,
  `Algebra.ClosedLift.exists_natural_homEquiv`; and
  `WeilConjectures.RingTheory.ProEtale.ClosedLift`,
  `Algebra.ClosedLift.bijective_reduction` (with the definition `reduction`).
- Proof import `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`,
  the recorded Mathlib match for `def-weil-affine-spectrum`.
The declaration docstring carries all three node proof steps: the natural affine
Hom correspondence, reversed algebra unit/counit and triangle identities, and the
invertible reduction giving a natural invertible site unit.

Sources checked: the item's entire blueprint page, Stacks proetale.tex,
`lemma-closed-immersion-affines` (Tag 09BK), statement and first proof paragraphs,
and `lemma-lift-ind-etale` (Tag 097P), statement and construction. In particular,
09BK asserts a fully faithful left adjoint and identifies V with its base change;
the invertible-unit formulation is exactly this part of that statement.

Edge cases: `I = ⊥`, `I = ⊤`, the zero ring A, and the empty affine object are all
included. The existing basis categories and functors handle empty schemes; no
nonemptiness is used. The universe `u` is arbitrary and inherited unchanged by
both functors. The canonical identity is an isomorphism, not equality of the
chosen pullback objects. No statement correction or dispute was needed.

Searches for an existing statement (2026-10-15):
- `msearch.py ... leanfinder`: “The closed lift functor on affine ind etale schemes
  is left adjoint to quotient base change with invertible unit”. Eight hits,
  including `Scheme.kerAdjunction`, `ΓSpec.adjunction`, and `Spec.reflective`;
  these concern different functors and do not state this node.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.op`. Eleven hits, including
  opposite adjunction and component formulas; these are generic tools, not this
  specific adjunction.
- `msearch.py ... grep`: `closedSite.*[Aa]dj|closed.*[Ll]ift.*[Aa]dj|[Aa]dj.*closedSite`.
  Zero Mathlib hits.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for closed-site adjunction names and the node id:
  no existing site-adjunction declaration. The only relevant adjunction module is
  the algebra-level `ClosedLiftAdjunction`, already imported as a proof dependency.
- Searched both upstream and project for `def-exc-closed-site-lift`: the recorded
  project module provides the functors, but no adjunction theorem. Checked the
  proposed full declaration name for collisions, with no hits.

Validation: single-file server compilation through `scompile.py`, using the
published library and side overlay; no local compiler or global build is used.
The delivery dry run is the final validation; the independent second reader writes
its own section after this worker's handoff.

## Second reading by NF

I independently read the node, its blueprint page (order 1844), the complete
recorded ClosedSiteLift dependency module, its basis category declaration, the
algebra Hom-equivalence declaration, and the reduction declaration. I also read
Stacks proetale.tex, lemma-lift-ind-etale (097P), statement and full proof, and
lemma-closed-immersion-affines (09BK), statement and proof. These sources assume
an arbitrary commutative ring and ideal, with affine bases; no Noetherian,
finiteness, nilpotence, proper-ideal, or nonzero assumption is implicit here.

The object/hypothesis/conclusion checklist, matched to the actual signature:

- Objects A, I, X = Spec A, Z = Spec(A/I): `A : Type u`, `[CommRing A]`,
  `I : Ideal A`; the two spectra are built into the recorded functors' types.
  Verdict: exact, with no extra hypothesis.
- Basis categories B_Z and B_X: the functors have domain and codomain
  `(Spec (.of (A ⧸ I))).AffineProEt` and `(Spec (.of A)).AffineProEt`.
  I checked `Scheme.AffineProEt = proAffineEtale.Over ⊤ S` in the recorded
  Comparison.Affine source: for these affine bases this is precisely the
  affine ind-etale basis of def-weil-pbc-ind-etale-basis. Verdict: exact.
- Functor v on objects and maps: `closedSiteLift A I` is the declaration
  of def-exc-closed-site-lift, taking Spec of the actual closed-lift algebra
  of global coordinates, and reversing the actual induced algebra maps.
  I read its coordinates, object, over-map, map and functor definitions.
  Verdict: the specified construction, with no private replacement.
- Functor u: `closedSiteBaseChange A I` is pullback along the spectrum of
  `Ideal.Quotient.mk I`. Verdict: precisely base change X to Z.
- Conclusion v left adjoint to u: `∃ adj : closedSiteLift A I ⊣
  closedSiteBaseChange A I`. Mathlib `Adjunction` includes natural unit,
  natural counit and both triangle identities. Verdict: exact direction
  and complete adjunction, universally for each A and I.
- Conclusion uv canonically identity: `IsIso adj.unit`, for the same adj.
  Its type is `𝟭 B_Z ⟶ closedSiteLift A I ⋙ closedSiteBaseChange A I`;
  hence its invertibility supplies the natural identification in the node.
  This is the adjunction-unit formulation in the blueprint proof and
  Stacks, rather than strict equality of chosen pullbacks. Verdict: exact.

Edge cases: the zero ring (empty X), I = top (empty Z), I = bottom, and
empty affine objects are all allowed by these binders and basis definitions.
In the empty-Z case the site still has its empty affine object; no Nonempty
or properness assumption was added. All characteristics are allowed. There
is no indexed family or degree n in this statement. The ring/scheme universe
u is arbitrary; AffineProEt has object universe u+1 and morphism universe u,
which Adjunction accepts independently. No equality of those universes, or
unbound variable, is present.

Independent duplicate searches used different queries from the first reader:

- `msearch.py NF lem-exc-closed-site-adjunction leanfinder` with
  "Base change of affine weakly etale schemes along a closed immersion has
  a fully faithful left adjoint": eight hits, concerning ordinary etale
  forgetful functors and etale stability, not the specified closed lift.
- `msearch.py ... loogle 'CategoryTheory.Adjunction, CategoryTheory.IsIso'`:
  twelve hits, including `Adjunction.fullyFaithfulLOfIsIsoUnit` and
  `Adjunction.toEquivalence`. These are general consequences of an
  already supplied adjunction, not this adjunction's existence.
- `msearch.py ... grep 'closed.*immersion.*adj|adj.*closed.*immersion|closedSite|closedLift'`:
  zero hits. Independently ran rg over Mathlib, upstream WeilConjectures,
  and project lean/Sheaf for closed/adjoint, closedSite and ClosedLift/adj
  variants. The pertinent results were the recorded lift definitions and
  the algebra-level ClosedLiftAdjunction; no existing site theorem matched.

No new nodes or dependency modules are included. The proof imports match
all recorded proof dependencies: the natural algebra Hom correspondence,
the specified invertible reduction, and contravariant Spec. The statement
has one named theorem with proof `sorry`, no definitions or hidden data
choices, and source/blueprint docstrings. Its proof docstring follows all
three DAG steps: natural Hom equivalence, reversed unit/counit and both
triangle identities, and the reduction isomorphism giving an invertible
natural unit. The node lean.statement is verbatim the file's signature.

Mismatches found: none. Changes: this independent second-reading report
only; retained the Lean module and node statement unchanged.

Validation: `scompile.py NF lem-exc-closed-site-adjunction
lean/Sheaf/AlgebraicGeometry/ProEtale/ClosedSiteAdjunction.lean` passed on
the server, with nice 19, two threads and the 60-second per-file limit;
the delivered file took 1.5 seconds. No errors or warnings were emitted.
