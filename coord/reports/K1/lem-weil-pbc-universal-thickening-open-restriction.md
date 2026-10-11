## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction` states the
restriction theorem for a universal first order thickening.  It binds schemes `Z`,
`X`, `Z'`, maps `h`, `i`, `h'`, the universal-thickening hypothesis `H`, and the
formal-unramified hypothesis `hform`.  For opens `V` and `U`, `hVU : V ≤ h ⁻¹ᵁ U`
expresses `h(V) ⊆ U`.  The conclusion supplies the unique restriction map `hV`
(`V.ι ≫ h = hV ≫ U.ι`) and formal unramifiedness of `hV`; an open `V'`, restricted
maps `iV` and `hV'`, the equalities `i ⁻¹ᵁ V' = V`, `V' ≤ h' ⁻¹ᵁ U`,
`iV ≫ V'.ι = V.ι ≫ i`, `hV' ≫ U.ι = V'.ι ≫ h'`, and `iV ≫ hV' = hV`; and the
universal first-order-thickening property of `hV`, `iV`, `hV'`.  Finally the
existential `hVform` records the formal-unramified instance needed by the conormal
definition, and `Nonempty` of the isomorphism between the restriction
`(Scheme.Modules.restrictFunctor V.ι).obj C_{Z/X}` and `C_{V/U}` is the conormal
identification.  The explicit `HV` existential supplies the universal-thickening witness for the
latter definition; no data definition contains `sorry`.

Dependencies used are `AlgebraicGeometry.IsUniversalFirstOrderThickening` from
`Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`,
`AlgebraicGeometry.FormallyUnramified` from Mathlib's
`AlgebraicGeometry.Morphisms.FormallyUnramified`,
`AlgebraicGeometry.formallyUnramifiedConormal` from
`Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal`, and open-subscheme and
first-order-thickening notions used by the imported modules.

Edge cases checked: `V` and `U` may be empty; no affine, finite-type, or
nonempty assumptions are introduced.  The theorem allows arbitrary schemes and
arbitrary opens, and retains the full universal lifting property (including its
compatibility equations) and the square-zero thickening through the dependency
notion.

Searches for an existing declaration: `msearch.py leanfinder` for “universal first
order thickening restricts to open subschemes and conormal sheaf” returned
`AlgebraicGeometry.FormallyUnramified` only; `msearch.py loogle` for
`IsUniversalFirstOrderThickening, formallyUnramifiedConormal` returned no matching
restriction theorem; `msearch.py grep` and `rg` over Mathlib, the source repository,
and `lean/Sheaf` found `universalFirstOrderThickening_open_pieces` (the related
open-pieces theorem) but no declaration of this node's restriction and conormal
statement.  Thus a new theorem module is required.

## Earlier second reading (a previous round; superseded)

The node and module were read together.  The Lean statement retains every source
hypothesis (`h` formally unramified, a universal thickening, and `h(V) ⊆ U`) and
all requested clauses: factorization through `U`, the corresponding open `V'`,
restriction equations, universality over `U`, and the conormal restriction
isomorphism.  The explicit `hVform` and `HV` existential binders only expose the
instances and witness already required by the conormal definition; they do not
add mathematical assumptions.  Empty opens and arbitrary (possibly non-affine)
schemes remain permitted.  No mismatch was found.

## Second reading by K1

Read the node copy, every statement dependency node and its recorded declaration,
and the actual module. The local Stacks checkout is absent on this machine, so
I fetched `more-morphisms.tex` from the Stacks repository into the sandbox and
read its labels `lemma-universal-thickening-localize` (04FA),
`lemma-formally-unramified-on-opens` (02HC), `lemma-universal-thickening` (04F3),
`section-universal-thickening` (04F2), and `definition-universal-thickening` (04F4).
The source has no standing Noetherian, affine, finite-type, separated, field,
or characteristic hypothesis here. The node agrees with the source.
Source links: https://stacks.math.columbia.edu/tag/04FA,
https://stacks.math.columbia.edu/tag/02HC,
https://stacks.math.columbia.edu/tag/04F3.

Objects, hypotheses, and conclusion clauses, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary schemes Z, X, Z' and h : Z → X | `{Z X Z' : Scheme.{u}} (h : Z ⟶ X)` | Exact; arbitrary universe u. |
| Chosen universal first order thickening Z ⊂ Z' over X | `(i : Z ⟶ Z') (h' : Z' ⟶ X)` and `H : IsUniversalFirstOrderThickening h i h'` | Exact; H contains a closed immersion, square-zero kernel ideal, i ≫ h' = h, and existence and uniqueness against arbitrary scheme thickenings, not only affine tests. |
| h formally unramified | `hform : FormallyUnramified h` | Exact via Mathlib's `FormallyUnramified.hom_ext` and `of_hom_ext`, read in the dependency's recorded file. No finite-type condition. |
| Open subschemes V ⊂ Z, U ⊂ X | `(V : Z.Opens) (U : X.Opens)` and their `toScheme`, `ι` | Exact canonical open subschemes; Mathlib's open immersion definition and open-subscheme constructions were inspected. |
| h(V) ⊂ U | `hVU : V ≤ h ⁻¹ᵁ U` | Exact pointwise containment. |
| Restricted h : V → U | `∃ hV`, with `V.ι ≫ h = hV ≫ U.ι` | Exact; the open inclusion is a monomorphism, so this specifies the unique restriction. |
| h restricted to V is formally unramified | `FormallyUnramified hV` | Exact first conclusion. |
| Corresponding open V' with V = Z ∩ V' | `∃ V' : Z'.Opens`, `i ⁻¹ᵁ V' = V` | Exact: a square-zero closed immersion is a homeomorphism on points, so this determines the unique V'. |
| V' maps into U by restricting h' | `V' ≤ h' ⁻¹ᵁ U`, `hV' ≫ U.ι = V'.ι ≫ h'` | Exact; containment is the condition for the restriction to exist. |
| V ⊂ V' is the restriction of i, over U | `iV ≫ V'.ι = V.ι ≫ i`, `iV ≫ hV' = hV` | Exact compatibility equations, not arbitrary new maps. |
| This thickening is universal over U | `IsUniversalFirstOrderThickening hV iV hV'` | Exact second conclusion, including square-zero condition and full unique lifting property. |
| C_{Z/X} restricted to V is isomorphic to C_{V/U} | `Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj (@formallyUnramifiedConormal ... h hform i h' H) ≅ @formallyUnramifiedConormal ... hV hVform iV hV' HV)` | Exact third conclusion in V.Modules; no canonical-section condition is asserted by the node. |
| Witnesses used to type the latter conormal | Existential `hVform` and `HV` | These repeat the established Prop conclusions, with proof irrelevance; no additional assumption or choice of new thickening is introduced. |

Dependency signatures were opened, not inferred from their names:
`IsUniversalFirstOrderThickening` is the full unique lifting predicate in
`UniversalFirstOrderThickening.lean`, built from `IsFirstOrderThickening` in
`Thickening.lean`. The latter is `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
`formallyUnramifiedConormal` in `FormallyUnramifiedConormal.lean` is exactly
`(Scheme.Modules.tensorPullback i).obj i.ker.toModules`; its data contains no
sorry. This uses the recorded tensor module pullback, not Mathlib's different
module pullback. Its independence theorem supplies choice independence.
`Scheme.Modules.restrictFunctor` in Mathlib's `Modules/Sheaf.lean` is actual
restriction along an open immersion. All recorded dependency notions are usable;
no new definition node or dependency module is needed.

Edge cases: empty V and U and empty schemes are allowed. If U is empty,
`hVU` forces V empty, as in the source. For V = top or U = top, the same
restriction equations still apply. Zero conormal modules and zero square-zero
ideals are allowed. There is no integer n, index set, field, characteristic,
or finiteness binder. All schemes and test schemes use the same arbitrary
universe u, as in the recorded universal-thickening definition; there is no
independent smaller test universe that could make the lifting condition vacuous.
No variable or universe is unbound.

Independent searches (different wording from the worker):

- LeanSearch: "conormal module of formally unramified scheme morphism commutes
  with open restriction"; service returned Internal Server Error, recorded as
  unavailable, not as a no-match result.
- Loogle: `"conormal"`; zero hits.
- LeanFinder: "restriction of square zero universal scheme neighbourhood to
  open subschemes preserves conormal module"; eight hits, all immersion or
  ideal-sheaf/open-subscheme constructions, no matching theorem.
- `msearch.py grep` in Mathlib/AlgebraicGeometry for
  `universal.*thicken|conormal|first.order.thicken`; zero hits.
- Independent `rg` with those terms over WeilConjectures/, lean/Sheaf/, and
  dag/lean_names_upstream.json: no source/upstream matching theorem. The landed
  `universalFirstOrderThickening_open_pieces` was opened in full: it provides
  restriction universality, but not the formal-unramified or conormal conclusion,
  so it does not realize this node. Existing conormal statements define the
  dependency or concern flat base change, not this statement.

Mismatches and repairs: no mathematical mismatch or node correction. The
statement docstring originally only summarized the argument, omitting the node's
five detailed proof steps; it now gives all five with their dependency names,
including the surjectivity argument for factoring test lifts and cancellation
for uniqueness. Added the standard license/author header. Removed the unused
`UniversalThickeningOpenPieces` import; the used definitions are already imported
by `FormallyUnramifiedConormal`. Corrected the worker report's stale reference
to an inline `by sorry` argument: the file actually binds HV explicitly.
The node's `lean.statement` was out of sync in whitespace and line wrapping;
refreshed it verbatim from the unchanged theorem signature. No statement,
statement dependency, or proof field changed. The only sorry is the named theorem
proof. No hollow definition, private notation, local instance, or proved theorem
was added. All lines of the Lean module are within 100 characters.

Validation: `scompile.py K1 lem-weil-pbc-universal-thickening-open-restriction`
compiled the complete delivery module cleanly in 1.8 seconds, exit code 0,
with no warnings. Dry run and delivery use the required deliver2.py checks.
