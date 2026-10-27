## Worker report

The module `Sheaf.AlgebraicGeometry.RationalFixedPointAffineness` states
`AlgebraicGeometry.isAffine_of_rational_fixed_point`. Its only theorem has proof
`sorry`. No definitions, helper axioms, dependency modules, or new nodes are added.
The item changes only in `lean`.

Source read: Milne, Algebraic Groups (2017), local PDF, printed pp.150 and 153–154,
Propositions 8.9 and 8.25. I extracted the PDF into the sandbox scratchpad. The
rational variant is expanded in Milne (2013), arXiv:1311.6060v2,
https://arxiv.org/html/1311.6060v2, Lemma 4.3 and the final paragraph of the proof
of Proposition 4.1. The latter uses the finite jets of the local ring at the fixed
point to obtain a faithful linear representation. These sources support the
node's rational variant, rather than requiring a regular action on all of X.
The module docstring gives the node's complete four-step proof, including the
finite affine-cover stabilization and scheme-theoretic kernel argument.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  No characteristic restriction is imposed.
- `G X Y : Over (Spec (.of k))` supplies all three k-schemes and their structure
  morphisms. `[GrpObj G]` supplies multiplication, inverse, and identity with
  the group diagrams. This is the recorded group-scheme encoding, not an
  assumption that G is affine.
- Smoothness is `[Smooth G.hom]`, connectedness including nonemptiness is
  `[ConnectedSpace G.left]`, and separatedness is `[IsSeparated G.hom]`.
- Finite type of G is the pair `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
  This is exactly the finite-type dependency's convention.
- Integrality of X, including nonemptiness and reducedness, is
  `[IsIntegral X.left]`; separatedness and finite type are
  `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- `j : Y ⟶ X` is a k-morphism, `[IsOpenImmersion j.left]` makes Y an open
  subscheme, `[Nonempty Y.left]` makes it nonempty, and
  `hdense : Dense (Set.range j.left)` asserts exactly density of that open.
  This allows a specified open immersion instead of identifying Y definitionally
  with a subtype; it is an equivalent presentation of the open subscheme.
- `[ModObj G Y]` supplies the morphism
  `ModObj.smul (M := G) (X := Y) : G ⊗ Y ⟶ Y`, with the identity and
  multiplication laws `ModObj.one_smul` and `ModObj.mul_smul`. The cartesian
  monoidal product on `Over (Spec (.of k))` is the scheme fibre product over k.
- `hfaithful` quantifies over every k-group scheme K, every inclusion `i : K ⟶ G`,
  and `[IsClosedSubgroupScheme i]`, the dependency's existing closed-subgroup class.
  Its premise `(i ⊗ₘ 𝟙 Y) ≫ smul = snd K Y` says that the restricted action
  K times Y to Y is the second projection. Equality of these morphisms implies
  equality after every commutative k-algebra base change; conversely the stated
  family includes base change by k itself. Thus this formulation is equivalent
  to the node's condition, with no restriction to reduced or field-valued points.
  Its conclusion `i = toUnit K ≫ η[G]` says that the closed inclusion factors
  through the identity subgroup. This is exactly that the subgroup is trivial:
  since i is monic and preserves identity, the unit of K and its structure map
  are inverse. Conversely the identity subgroup has this factorization. No
  assertion about the underlying set alone substitutes for this equality.
- `α : (G ⊗ X).left.PartialMap X.left` uses Mathlib's genuine partial-map
  structure: a dense open domain and a morphism on it. The associated rational
  map is `α.toRationalMap`, Mathlib's equivalence class of partial maps agreeing
  on a dense open. `hmax : α.domain = α.toRationalMap.domain` requires its
  representative to be on the largest domain, the supremum of all representatives'
  domains. Thus no arbitrary smaller domain is substituted for Dom(alpha).
- `hextends` asserts the existence of the open-domain factorization t of
  `𝟙 G ⊗ₘ j`, with `t ≫ α.domain.ι = (𝟙 G ⊗ₘ j).left` and
  `t ≫ α.hom = (smul ≫ j).left`. Its first equation says the entire G times Y
  lies in Dom(alpha); its second says the restriction is precisely a followed by
  Y into X. The factorization is unique because the open inclusion is monic.
  This is the rational extension in the node. Such an extension is uniquely
  determined on G times Y. The presentation by a maximal partial map adds no
  existence assumption: G times X is reduced (G is smooth over k, X is integral),
  and X is separated, so the canonical representative on the largest domain
  exists. X is also absolutely separated since Spec k is affine separated.
  Although PartialMap is unbundled over k, its representative is a k-map:
  the two structure maps to Spec k agree on the dense G times Y and hence
  agree everywhere on the reduced domain. This imposes no extra hypothesis.
- `P : 𝟙_ (Over (Spec (.of k))) ⟶ X` is a k-rational point: the terminal
  object's underlying scheme is Spec k with its identity structure map.
- `hdefined` requires `(lift η[G] P).left`, the rational point (e,P) of
  G times X, to factor through `α.domain.ι`. For an open subscheme this is
  equivalent to (e,P) belonging to the domain. No lifting hypothesis about a
  thickening or an entire neighbourhood of the fixed section is added.
- `hfixed` quantifies over every test k-scheme T, every `g : T ⟶ G`, and every
  map `d : T.left ⟶ α.domain.toScheme`. Its premise
  `d ≫ α.domain.ι = (lift g (toUnit T ≫ P)).left` makes d the factorization
  of (g,P) into the domain. Such test maps are exactly maps to
  V = (g ↦ (g,P)) inverse-image of Dom(alpha). Its conclusion
  `d ≫ α.hom = (toUnit T ≫ P).left` is equality with the constant P map.
  By testing on V itself, this is precisely equality of the morphisms on V,
  hence the stated equality on V times {P}. Conversely that morphism equality
  implies every displayed test equality. Arbitrary nonreduced T are included.
- The conclusion is `IsAffine G.left`, Mathlib's affineness class, equivalent
  to being isomorphic to Spec of its global ring of functions. Since G is a
  k-scheme that ring is canonically a k-algebra, as required by the node.
- The boilerplate convention about topological Krull dimension introduces no
  dimensional hypothesis or conclusion in this item; no dimension expression
  is needed. Likewise no global regular action on X is postulated anywhere.

Dependency interfaces read and used (including their full signatures/docstrings):

| Node | Module / declaration |
| --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs / Field |
| def-weil-algebraic-closure | Mathlib.FieldTheory.IsAlgClosed.Basic / IsAlgClosed (the algebraically closed-field part of mathlib_match) |
| def-sc-group-scheme | Mathlib.CategoryTheory.Monoidal.Grp / CategoryTheory.GrpObj, with WeilConjectures.AlgebraicGeometry.GroupScheme.Defs's explicit Over Spec k convention |
| def-sc-group-scheme-subgroup | WeilConjectures.AlgebraicGeometry.GroupScheme.Defs / AlgebraicGeometry.IsClosedSubgroupScheme, extending IsSubgroupScheme and IsMonHom |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth / AlgebraicGeometry.Smooth |
| def-weil-connected-scheme | Mathlib.Topology.Connected.Basic / ConnectedSpace, from mathlib_match; there is no lean record and none is needed |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType / LocallyOfFiniteType, and Morphisms.QuasiCompact / QuasiCompact |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper (and Separated) / IsSeparated; properness itself is not assumed |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension / topologicalKrullDim; read, but no dimension occurs in the mathematical assertion |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties / IsIntegral |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback / pullback, fst, snd; presented by the existing cartesian tensor on Over |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme / Scheme, Scheme.Hom; Mathlib.AlgebraicGeometry.AffineScheme / IsAffine |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion / IsOpenImmersion |

Additional existing interfaces: Mathlib.CategoryTheory.Monoidal.Mod / ModObj and
its smul, one_smul, mul_smul; Mathlib.AlgebraicGeometry.Birational.RationalMap /
Scheme.PartialMap, PartialMap.toRationalMap, Scheme.RationalMap, RationalMap.domain;
Mathlib.CategoryTheory.Monoidal.Cartesian.Basic / lift, snd, toUnit.
No private copy of any notion is introduced.

The already-stated proof dependencies are imported without `public`:
Mathlib.AlgebraicGeometry.Noetherian (finite type over a Noetherian base and
pqf-def-locnoeth), Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion (the affine
cover criterion), Mathlib.RingTheory.Noetherian.Defs,
Sheaf.AlgebraicGeometry.LinearGroupSchemes, and
Sheaf.AlgebraicGeometry.GroupScheme.MonomorphismClosedImmersion. The jet and
constant-family jet-equality proof-dependency nodes have no Lean record yet;
there is no module to import for them. They are not statement prerequisites.

Edge cases checked before drafting: the empty X is excluded by integrality;
the empty Y is excluded explicitly, and the empty group by the group unit and
connectedness. The identity group is allowed and the conclusion is correct.
A zero-dimensional X (over k, a point) forces a faithful G to be trivial, so no
positive-dimensional assumption is added. P may lie outside Y. A non-affine G
is permitted in the hypotheses. G and X need not be projective or proper, and X
need not be smooth or normal. Nonreduced closed kernels and all characteristics
are retained. Test schemes, rings, and schemes inhabit the same arbitrary
universe u; in particular V itself is an available test object and tests cannot
become vacuous through a smaller independent universe.

Searches performed for an existing exact assertion:

- msearch.py leanfinder: "A faithful rational action of a smooth connected
  algebraic group fixing a rational point implies the group is affine".
  Eight hits: affine-space and quasi-affine instances and abstract finite-type
  group-action results; no scheme-theoretic rational fixed-point criterion.
- msearch.py leansearch: "A faithful algebraic group action with a fixed point
  implies that the group is affine". Eight hits: FixedPoints algebra automorphism
  results, IsGaloisGroup, and FaithfulVAdd / abstract faithful action statements;
  none states this assertion.
- msearch.py loogle: `"RationalMap"`. Found the existing RationalMap, PartialMap
  conversion, largest domain, and canonical maximal representative API. Reused
  those objects instead of introducing a rational-map definition.
- msearch.py grep: `rational.*action|fixed.*affine|ModObj` under AlgebraicGeometry:
  zero hits. The categorical ModObj was found separately in
  Mathlib/CategoryTheory/Monoidal/Mod.lean; its full class was read.
- rg searches in lean/WeilConjectures and lean/Sheaf for
  `rational.*action|fixed.*affine|isAffine.*fixed`: no matching criterion;
  returned incidental comments about fixed affine charts and rational coefficients.
  `grep -rn lem-sfb-rational-fixed-point-affineness lean/WeilConjectures`:
  no declaration attached to this node. Searches for
  `rational_fixed_point|RationalFixedPointAffineness` in Mathlib and
  dag/lean_names_upstream.json found no collision.
- Searched DAG definition nodes and current project modules for rational actions
  and fixed-point affineness. No existing definition needs replacement; the
  required action and rational-map objects are already Mathlib interfaces.

No statement fault or STATEMENT-DISPUTED flag was found. No source-based
correction is needed. The old CompactObject example is withdrawn locally;
I read its node's current existing record and the actual upstream
WeilConjectures.CategoryTheory.CompactObject module for the module/docstring style.

Validation: the initial server compile caught positional arguments to the
implicit-argument projection ModObj.smul; changed both uses to named arguments.
The subsequent sandbox and library-module server checks both passed cleanly
(2.7 s and 2.5 s). The final autoImplicit=false setting and explicit proof
import are also validated by the delivery dry run; no proof other than sorry
is present.

## Second reading by Q97

This is the author's second reading, not an independent review; the dispatcher
explicitly forbids starting other agents and the maintainer supplies the
independent reading. I reopened the node and final Lean declaration. The field,
group laws, smoothness, nonempty connectedness, separatedness, both finite-type
conditions, integrality, nonempty dense open immersion, unit/multiplication action
laws, all closed subgroup schemes, scheme-theoretic faithfulness, dense rational
map and largest domain, extension of the action, rational point, definition at
(e,P), and equality with P on precisely the defined fixed section each have
the binders or equations enumerated above. IsAffine is the entire conclusion.
I specifically checked that hmax is not omitted, that P is not required to lie
in Y, that hdefined only concerns (e,P), and that hfixed neither assumes the
whole G times P lies in the domain nor reduces morphism equality to closed
points. The factorization formulations are equivalent presentations, not
stronger hypotheses. No mismatch was found on this pass; no mathematical
change to the node or declaration was necessary. The only elaboration repair
was the named arguments to smul described above. All variables and the single
universe are explicitly bound, with autoImplicit disabled.

## Recovery validation, 2026-10-24

Retained the saved packet and ran the prescribed `deliver2.py Q97
lem-sfb-rational-fixed-point-affineness --no-push` twice. Both exited 1
during server compilation, reporting the same infrastructure failure for
`Sheaf.AlgebraicGeometry.RationalFixedPointAffineness`:
`resource exhausted (error code: 28, no space left on device)`.
Neither run pushed anything. No Lean diagnostic identified a statement repair.
The current repository node still has no Lean record; the saved node differs
only in `lean`, its recorded signature matches the source verbatim, and every
Lean line is at most 100 characters. The saved source and node are unchanged.
Server storage remains the blocker; no server files or launcher tools were
modified.

## Dispatcher recovery retry, 2026-10-24

Inspected the retained report and module, then ran the required dry run before
attempting any changes. Both this dry run and its retry failed with exit 1:
`library Sheaf.AlgebraicGeometry.RationalFixedPointAffineness` reported
`resource exhausted (error code: 28, no space left on device)` (2.1 seconds),
after the sandbox check (14.2 seconds). Both explicitly reported nothing pushed.
The current item still has no lean record or repair note. Rechecked that only
`lean` differs from the current node, the complete signature before the theorem's
final `:=` matches the recorded statement verbatim, the longest Lean line has
89 characters, and autoImplicit is disabled with the universe explicitly bound.
The source and node remain unchanged. No statement diagnostic calls for a repair;
the server storage/tool failure prevents the required passing dry run and push.

## Latest dispatcher recovery, 2026-10-24

Read the saved report and ran the prescribed dry run, then retried it once.
Both runs failed with exit 1 during the library compile with exactly
`resource exhausted (error code: 28, no space left on device)` for
`Sheaf.AlgebraicGeometry.RationalFixedPointAffineness` (2.1 seconds), following
the sandbox check (14.2 seconds). Both reported nothing pushed. There was no
Lean statement diagnostic to repair. Reopened the saved source and node and
verified against the current read-only repository: only `lean` differs, the
signature matches verbatim, autoImplicit is disabled, the universe is explicitly
bound, the maximum line length is 89, and there is no current repair note.
Retained the source and node unchanged; did not modify server storage or tools.
The repeated server storage failure prevents a passing dry run and delivery.

## Current recovery verification, 2026-10-24

Inspected the retained packet and ran `deliver2.py Q97
lem-sfb-rational-fixed-point-affineness --no-push` twice. Both exited 1
with `resource exhausted (error code: 28, no space left on device)` in the
server library compile after the sandbox check. A separate prescribed
`scompile.py` call gave the same diagnostic. No Lean elaboration diagnostic
was produced and nothing was pushed. Local storage has ample free space;
no server storage or launcher tools were modified. Verified against the
current read-only node that only `lean` differs and that the recorded signature
matches the saved source verbatim (maximum line length 89). Retained the Lean
source and node unchanged. The server compilation/storage failure remains
the obstacle to delivery.

## Recovery dry runs, 2026-10-24 10:55 UTC

Inspected the retained report first and ran the required deliver2.py dry run,
then retried it once. Both exited 1 with nothing pushed. Each reported
`resource exhausted (error code: 28, no space left on device)` during
the library compile of `Sheaf.AlgebraicGeometry.RationalFixedPointAffineness`
(2.1 seconds), after the sandbox check (14.2 seconds). No Lean elaboration
diagnostic was produced. Checked the current read-only node against the
saved packet: only `lean` differs; its signature matches the source before
the `:=` delimiter; autoImplicit is disabled and the maximum line length
is 89. No repair-note file exists for this item. Retained the source and
node unchanged. No server storage, shared source, or launcher tools were
modified. Delivery remains prevented by the server storage/tool failure.

## Retained-packet retry, 2026-10-24 10:58 UTC

Inspected the saved report and ran the required deliver2.py dry run, then
retried it once. Both exited 1 with nothing pushed, reporting
`resource exhausted (error code: 28, no space left on device)` during
the server library compile (2.1 seconds) after the sandbox check
(14.2 seconds). No Lean elaboration diagnostic was produced. Compared
the saved node with the current shared node: only `lean` differs, the
recorded theorem signature matches the source verbatim, autoImplicit
is disabled, the universe is explicitly bound, and maximum line length
is 89. Retained the source and node unchanged. No server storage, shared
source, or launcher tool was modified. The repeated server storage
failure prevents the required passing dry run and delivery.

## Recovery verification, 2026-10-24 11:02 UTC

Read the retained report and ran the prescribed dry run, then retried once.
Both failed with nothing pushed: the server library compile reported
`resource exhausted (error code: 28, no space left on device)` after the
sandbox check. No Lean statement diagnostic was produced. Rechecked the
current node: only `lean` differs, the recorded signature matches verbatim,
autoImplicit is disabled, the universe is explicit, maximum line length is
89, and no repair note exists. Retained the source and node unchanged.
The server storage failure prevents a passing dry run and delivery.

## Dispatcher retained-packet verification, 2026-10-24 11:07 UTC

Read the saved report and ran the prescribed deliver2.py dry run first.
A direct scompile.py check and a second dry run after a short interval all
reproduced the same server library-compile failure: `resource exhausted
(error code: 28, no space left on device)` after the sandbox check. Both
dry runs exited 1 and explicitly reported nothing pushed. No Lean elaboration
diagnostic was produced. Rechecked the current shared node: only `lean`
differs, the recorded signature is verbatim, autoImplicit is disabled,
the universe is explicit, and the maximum line length is 89. Local storage
has ample free space. Retained the source and node unchanged; no shared
source, server storage, or launcher tools were modified. The persistent
server compile/storage failure prevents the required passing dry run.
