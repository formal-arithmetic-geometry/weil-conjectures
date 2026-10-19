## Worker report

The module `Sheaf.AlgebraicTopology.KanFibrantPathRecognition` states
`SSet.Enhanced.kan_fibrant_path_recognition`, with proof `sorry` only. It introduces
no definitions. The node's statement, proof, and proof dependencies are unchanged;
`stmt_deps` gains the already landed `def-coef-infinity-relative-cone` because its
`homotopyPullbackComparison` is exactly the canonical map required here.

Clause-by-clause rendering:

- Small simplicial sets: `{Q X Y Z : SSet.{u}}`, with explicitly declared universe
  `u`. Maps `a`, `b`, `f`, `g` have the node's domains and codomains. The binder
  `h : a ≫ f = b ≫ g` is the commutativity condition (Lean writes composition
  in diagrammatic order).
- The homotopy-cartesian condition is the entire left-hand existential. `Xf`,
  `Yf`, `i`, `j`, `ff`, `gf` are the two factorizations over the ORIGINAL base
  `Z`; `i ≫ ff = f` and `j ≫ gf = g` enforce the factorizations. Both `i` and
  `j` satisfy `IsWeakHomotopyEquivalence`, and both `ff` and `gf` satisfy the
  horn-defined `Fibration` predicate. The existential `c : Q ⟶ pullback ff gf`
  is fixed uniquely by its two projection equations, so it is precisely the
  induced map, not an arbitrary weak equivalence with this source and target.
  The final conjunct requires this map to be a weak homotopy equivalence.
- Any functorial fibrant replacement: `R : SSet.{u} ⥤ SSet.{u}` and
  `r : 𝟭 SSet.{u} ⟶ R` give both the endofunctor and natural replacement map.
  `hr` says every component is a monomorphism and a realization weak homotopy
  equivalence. These are exactly trivial cofibrations in the specified
  Kan--Quillen structure, by `right_proper_kan_quillen_core` (its cofibrations
  are monomorphisms and its weak equivalences are the realization predicate).
  `hR` makes each `R.obj T ⟶ Δ[0]` a Kan fibration. The factorization equation
  for the original terminal map follows from terminal uniqueness. No extra
  preservation property of `R` is assumed.
- The right side uses `homotopyPullbackComparison (R.map a) (R.map b)
  (R.map f) (R.map g)` from the landed relative-cone node. Its target is
  `simplicialHomotopyPullback (R.map f) (R.map g)`, definitionally the nested
  pullback `RX ×_(RZ,ev₀) Fun(Δ[1],RZ) ×_(ev₁,RZ) RY`. This construction
  uses the recorded `evaluation` maps at vertices 0 and 1. Its coordinates
  are `Ra`, the constant path at `Ra ≫ Rf`, and `Rb`, by the actual nested
  `pullback.lift` definition, which I read in `RelativeInfinityCone.lean`.
  The equality witness `(R.map_comp a f).symm.trans
  ((congrArg R.map h).trans (R.map_comp b g))` is functorial commutativity,
  and carries no additional hypothesis. `IsWeakHomotopyEquivalence` of this
  exact map is the right side of the claimed `↔`.
- No `KanComplex`, `Nonempty`, selected point, size equality, or hypothesis on
  an original corner is introduced. All variables and the universe are bound;
  `set_option autoImplicit false` enforces this.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `evaluation`, and
  `constantDiagrams`. The weak equivalence uses bijectivity on realization
  path components and all positive based homotopy groups; it is not a
  simplicial-homotopy-equivalence substitute.
- `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore`:
  `SSet.KanQuillen.right_proper_kan_quillen_core`; the full signature and
  proof docstring were read. Imported for the proof plan and the equivalence
  between the replacement hypotheses and trivial-cofibration/fibration
  factorization.
- Added landed dependency `def-coef-infinity-relative-cone`, module
  `Sheaf.CategoryTheory.RelativeInfinityCone`:
  `SSet.Enhanced.homotopyPullbackComparison`. Its full signature and actual
  construction were read. Its inherited path object is
  `SSet.Enhanced.simplicialHomotopyPullback` in
  `Sheaf.CategoryTheory.SourceAttachmentGluing`, whose full definition and
  source docstring were also read. Neither construction assumes Kan corners.
- Proof imports: `Sheaf.AlgebraicTopology.KanPullbackFibrationInvariance`
  (`SSet.Enhanced.isWeakHomotopyEquivalence_pullback_map`),
  `Sheaf.AlgebraicTopology.KanPullbackPathComparison`
  (`SSet.Enhanced.kan_pullback_path_comparison`), and
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`
  (`SSet.fibration_pullbackObjObjπ`). Their signatures and proof docstrings
  were read. The Mathlib leaf is used through its `mathlib_match`, with no
  replacement node or duplicate declaration.

The existing `SSet.IsHomotopyCartesian` in `SharpPullbackCalculus.lean` has
exactly the expanded left-hand condition. It belongs to the downstream
`lem-coef-sharp-pullback-calculus`, whose proof uses the present recognition
lemma. Importing it would prevent that future proof import by closing a
cycle. The theorem therefore writes the node's existential condition directly;
no second predicate is defined. I also checked the transitive side imports of
`RelativeInfinityCone`: none imports `SharpPullbackCalculus` or this module.

Edge cases checked before writing:

- Empty `Z`: maps to `Z` force `Q`, `X`, `Y` empty. Replacement weak
  equivalences force their replacements empty too; the path pullback is empty.
  No dimension-zero horn or point assumption is used.
- Empty `X` or `Y` with nonempty base: its replacement stays empty up to the
  realization component condition, so the path target is empty and the
  corresponding two-leg target also models the empty homotopy pullback.
- Empty `Q` and a nonempty path target: the component-bijection test fails;
  there is no vacuous universal basepoint test in place of the component clause.
- Identity maps, terminal objects, disconnected bases, empty homotopy fibers,
  and non-Kan original corners are all admitted by the binders. In particular,
  the theorem makes no assertion that an arbitrary strict pullback over a
  non-Kan base is already a homotopy pullback.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A square of simplicial sets is homotopy
  cartesian if and only if functorial Kan replacement maps by a weak equivalence
  to the internal path pullback” returned eight hits on model lifting, path
  objects, Whitehead results, and truncated homotopy categories. None states
  this arbitrary-base two-leg recognition equivalence.
- `msearch.py ... leansearch`: “A homotopy cartesian square of simplicial sets
  is recognized by the path pullback after functorial Kan fibrant replacement”
  returned eight hits on bicartesian squares, path objects, and finite pullbacks;
  no exact match.
- `msearch.py ... loogle`: `HomotopicalAlgebra.PathObject,
  HomotopicalAlgebra.WeakEquivalence` returned five abstract path-object and
  right-homotopy hits, none this recognition theorem.
- `msearch.py ... grep`: `homotopy.?[Cc]artesian|homotopy.?[Pp]ullback` in
  `AlgebraicTopology` returned zero hits. Search receipts are in this sandbox.
- `rg` in upstream `WeilConjectures` for homotopy-cartesian terminology and
  `grep -rn` for the exact node id returned no match. Searches in project
  `lean/Sheaf` found the downstream factorization predicate, the Kan-only
  recognition theorem, and the usable existing canonical comparison above;
  no theorem equivalent to the item. Searches for the new declaration name
  in Mathlib, upstream, the side library, and `dag/lean_names_upstream.json`
  found no collision.

Sources checked: the current blueprint proof of
`prop-coef-integral-exceptional-adjoint`, paragraph 2; the node's six-step
agent expansion; and Rezk Section 2.3, printed p. 4, read at
https://rezk.web.illinois.edu/rezk-sharp-maps.pdf. Rezk's definition has exactly
weak-equivalence/fibration factorizations of both original legs. The comparison
proof is the explicitly identified agent expansion in the node, not a claim
that Rezk states this particular formula.

No statement correction, new node, dependency repair, or statement dispute.
The only postponed proof is `SSet.Enhanced.kan_fibrant_path_recognition`; its
complete six-step proof plan is in the declaration docstring.

## Second reading by Q35

Independent maintainer reading of immutable delivery `275d50965ef922995e28b07fa506c3691d0239c3`. The original worker supplied no second reading; this section records the independent review. The Lean and node need no change.

### Scope and sources

Read packet.md first, then check-brief2.md in full, snapshot/AGENTS.md,
coord/brief-stage2.md, delivery-errors.md section H, and stages/2-statements.md.
Read the immutable item node, its six proof steps, all three statement-dependency
nodes and their Lean records, the entire delivered Lean file and report. Dependency
source modules were read from the permitted read-only Q35 clone; Mathlib sources
were read from the permitted slopmaster2 clone.

Read the blueprint source
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2 and the displayed derived coefficient adjunction. This is the ancestor
motivation, not a claim that the blueprint itself states this simplicial theorem.
Read Rezk, *Fibrations and Homotopy Colimits of Simplicial Sheaves*, §2.3,
printed p. 4, via the indexed primary-source PDF text at
https://rezk.web.illinois.edu/rezk-sharp-maps.pdf (direct opening encountered a
verification page; the primary-source search result supplied §2.3 and Lemma 2.5).
Rezk uses weak-equivalence/fibration factorizations of both legs over the original
base. The interval formula and the six-step comparison are explicitly agent-origin
in the node, and the proof plan correctly supplies this additional comparison.

## Clause-by-clause reading

1. Small simplicial sets and maps: `{Q X Y Z : SSet.{u}}`, followed by `a`, `b`,
   `f`, `g`, have exactly the specified domains and codomains. The single arbitrary
   universe `u` is explicit; `autoImplicit false` excludes hidden binders.
2. Commutativity: `h : a ≫ f = b ≫ g` is exactly `fa = gb` in Lean's diagrammatic
   composition order.
3. Homotopy cartesianness: the left existential binds `Xf Yf i j ff gf` over the
   ORIGINAL `Z`. The equations `i ≫ ff = f`, `j ≫ gf = g`, the two realization weak
   equivalences, and the two Kan fibrations are all present. No cofibration or
   fibrancy condition is imposed on these particular replacements.
4. The induced map: the existential `c : Q ⟶ pullback ff gf` has both prescribed
   projections `a ≫ i` and `b ≫ j`. Pullback uniqueness fixes it completely; this
   is equivalent to requiring the canonical induced map to be weak, not an
   arbitrary weak map between these objects.
5. Functorial fibrant replacement: `R` is an endofunctor and `r` is a natural
   transformation from the identity. `hr` requires precisely a monomorphism and
   realization weak equivalence at every object; by the core model theorem these
   are trivial cofibrations. `hR` requires the terminal map of each `RT` to be a
   Kan fibration. Terminal uniqueness supplies the factorization equation. This
   expresses any such replacement, without an extra preservation assumption on R.
6. The path target is the existing `simplicialHomotopyPullback (R.map f) (R.map g)`.
   SourceAttachmentGluing.lean:88 constructs the inner pullback using endpoint 0
   and the outer one using endpoint 1, exactly the displayed P_R.
7. The right-hand map is `homotopyPullbackComparison` from RelativeInfinityCone.lean:75.
   Read its complete nested `pullback.lift` implementation: the coordinates are
   `Ra`, `(Ra ≫ Rf) ≫ constantDiagrams Δ[1] RZ`, and `Rb`. The supplied equality
   follows from `R.map_comp` and `congrArg R.map h`. Its source is RQ. The conclusion
   is weak equivalence of THIS map, in both directions of the required iff.
8. No Kan, inhabitance, connectedness, selected point, or other assumption is
   added on Q, X, Y or Z. No conclusion clause is dropped or strengthened.

## Dependencies and proof plan

EnhancedDiagramsCones.lean:75–96 defines the component and based homotopy-group
maps and `IsWeakHomotopyEquivalence`. It includes component bijectivity, so empty
source cases are not accepted vacuously. Lines 123–130 construct endpoint evaluation
and constant diagrams using the existing internal hom. These are the node's notions.

Read `SSet.KanQuillen.right_proper_kan_quillen_core` and its entire proof docstring
in KanQuillenModelRightProperCore.lean. Its model structure installs precisely the
realization predicate, has functorial factorizations, mono cofibrations, horn
fibrations and arbitrary-base right properness. Read CategoryWithFibrations.lean:
`J` ranges over all positive-dimensional horns including outer horns, with no
zero-dimensional nonemptiness condition. This validates both `hr` and `hR`.

Read RelativeInfinityCone.lean and the relevant SourceAttachmentGluing construction.
The comparison is real data, not a chosen arbitrary map or a hollow definition.
Read the exact signatures and proof docstrings of
`isWeakHomotopyEquivalence_pullback_map` (KanPullbackFibrationInvariance.lean:69),
`kan_pullback_path_comparison` (KanPullbackPathComparison.lean:74), and
`SSet.fibration_pullbackObjObjπ` (Mathlib PushoutProduct.lean:70–93).
The first requires both left legs fibrations and objectwise weak equivalences,
without Kan objects. The second requires the three Kan objects and either leg
fibrant. The third requires a mono and a Kan fibration only. All hypotheses are
available in their six-step applications.

Checked the proof plan mathematically: right properness gives K→U and L→V;
lifts under X,Y compare every admissible pair with K,L; pullback invariance compares
K×_Z L with U×_C V; the endpoint-pair fibration makes E_B→C and E_V→C fibrations;
E_B→E_V is the pullback of beta along E_V→V; invariance gives phi; the constant-path
lemma gives psi. Naturality gives w c_0 = d r_Q and the coordinate formulas give
phi c = psi d. Two-out-of-three yields exactly the claimed iff. No unstated DAG
prerequisite or universe repair is needed.

## Uniqueness, edge cases and pilot gates

Independent LeanSearch and LeanFinder queries used different phrasings about derived
fibre products, interval exponentials and replacement of all four vertices. Results
were ordinary pullback square lemmas, horn-fibration facts and abstract PathObject
facts, not this theorem. Read Mathlib PathObject.lean's definitions to distinguish
them. Independent rg searches of project Lean, upstream WeilConjectures and Mathlib
found no equivalent theorem or declaration-name collision. Read the nearby
KanHomotopyPullbackInvariance theorem: it assumes Kan corners and states invariance,
not the present recognition theorem. The downstream SharpPullbackCalculus predicate
has the same existential condition; spelling it out here defines no second predicate
and avoids the downstream proof-dependency cycle. The item's added statement
dependency is the already landed relative-cone node, allowed by §5. Its declaration
is used directly. A source import-closure check found 83 modules, no cycles or missing
side modules, and no SharpPullbackCalculus import.

Empty Z forces X,Y,Q empty; replacement weak equivalences preserve emptiness and
P_R is empty. An empty X or Y similarly yields an empty path target. Empty Q with
nonempty target fails component bijectivity. Disconnected bases, terminal and identity
maps, non-Kan original corners and empty fibres are covered. All constructions remain
in SSet.{u}; no silent equality of independent universes is imposed.

There is one declaration and one `sorry`, with no local proof beyond it and no new
definitions. Source/blueprint module and theorem docstrings are present, with all six
proof steps. Imports cover the stated and proof dependencies, including the Mathlib
leaf. No line exceeds 100 characters. The JSON `lean.statement` is byte-for-byte equal
to the source signature from `theorem` to before `:= by`. Required record fields are
present. No statement correction, citer audit, new node or dependency repair is needed.
This is simplicial homotopy theory; no pro-etale substitute is involved.

## Compiler evidence

The immutable worker report contains no explicit compile command/result receipt;
therefore its compilation was independently reproduced, rather than inferred.
Ran exactly:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q35 lem-coef-kan-fibrant-path-recognition snapshot/lean/Sheaf/AlgebraicTopology/KanFibrantPathRecognition.lean
```

Exit 0, no diagnostics. The current authorized wrapper reports server-side private
overlay compilation: sandbox `Sheaf/Stage2/Sandbox0.lean` 1.4 s, then library
`Sheaf/AlgebraicTopology/KanFibrantPathRecognition.lean` 1.6 s, under the default 60 s
per-file limits. Its output names private artifact directory
`/dev/shm/nt-tmp/nt-local-compile-rp6km5jf/.lbuild`.
The installed scompile.py currently dispatches the overlay to the server; this is
recorded accurately rather than described as a local invocation of lcompile.py.
Only this one Lean file is delivered. The fix changes report prose only, so no
additional compilation is needed.


Finding repaired (H11): replaced the original second-reading placeholder with the substantive reading above. No mathematical mismatch was found. The complete worker report is preserved. Only this report is replaced.
