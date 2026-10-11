## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine` states
`AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple` with its sole proof `sorry`.
No definition is introduced, and no node statement is corrected.

Hypothesis and conclusion correspondence:
- The scheme X is `(X : Scheme.{u})`, with explicit arbitrary universe `u`.
- The invertible O_X-module L is `(L : X.Modules) [L.IsInvertible]`.
- Ampleness is `(hL : Modules.IsAmple X L)`, the dependency's absolute ampleness condition.
  Its quasi-compactness requirement is already part of that recorded definition.
- An arbitrary finite subset E of the underlying space is `(E : Set X) (hE : E.Finite)`.
- Existence of an open U in X is `∃ U : X.Opens`.
- Affineness is `IsAffineOpen U`, the Mathlib predicate that the induced open scheme is affine.
- Containment is `E ⊆ (U : Set X)`.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (the mathlib leaf def-pc-scheme); only Scheme is needed by this statement.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, locally trivial with fibre O_X.
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
  This sole direct import supplies both preceding dependencies transitively.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen`.
  This is also supplied by the ample module's import.

Source checked: https://stacks.math.columbia.edu/tag/01ZY, case (3), whose conclusion is
precisely the node's. The local literature/stacks-project/properties.tex is absent, so the
Stacks page was opened directly. The docstring follows all four recorded proof steps and
names their dependencies. No new statement hypothesis is needed.

Edge cases checked before writing: E empty (the empty open scheme is affine); X empty
(then E is empty); singleton E (the conclusion agrees with the affine neighbourhood
condition); finite E containing nonclosed points (no closedness hypothesis is introduced).
No field, characteristic, Noetherian, separation, properness, nonemptiness or dimension
restriction is imposed. All schemes in arbitrary universe u are covered.

Searches for existing statements:
- msearch.py leansearch, query `scheme with ample invertible sheaf every finite set lies in
  affine open`: unavailable, Internal Server Error.
- msearch.py leanfinder, query `scheme ample line bundle finite subset contained in affine
  open`: eight hits concerning affine covers, quasi-affine schemes and standard Proj opens;
  none is this statement.
- msearch.py loogle, query `AlgebraicGeometry.IsAffineOpen`: twelve hits, confirming the
  existing affine-open predicate, but no ample finite-subset theorem.
- msearch.py grep, query `ample|finite.*affine|affine.*finite`, AlgebraicGeometry:
  affine cover and finite morphism results, no absolute ample finite-subset theorem.
- rg searches over WeilConjectures for ample, finite sets/subsets, and the node id, and
  over lean/Sheaf for ample and finite affine opens, found no exact statement.
  The source's `Scheme.exists_affineOpens_forall_mem_of_curve` in Hilbert/Curve.lean
  requires a geometrically integral smooth proper curve, so is strictly specialized.
  Upstream `AlgebraicGeometry.IsAmple` in Modules/Ample.lean is relative to a field and
  requires a projective scheme; it is not the recorded absolute ampleness notion.
- rg of the proposed declaration name in Mathlib/AlgebraicGeometry, lean/Sheaf and
  dag/lean_names_upstream.json found no name collision.

No STATEMENT-DISPUTED issue, missing notion or unusable dependency was found.

## Second reading by C1

I independently opened the sandbox node and module, all three statement-dependency
nodes, the imported Ample module, the upstream Invertible module, and Mathlib's
IsAffineOpen definition. The item has no statement_change, new definition nodes,
or dependency modules. No mismatch was found; the Lean and node are unchanged.

Object, hypothesis, and conclusion checklist (each passes):
- X is an arbitrary scheme: `(X : Scheme.{u})`, using the Mathlib scheme of
  def-pc-scheme, not a scheme over a field or a curve.
- L is an O_X-module: `(L : X.Modules)`. This is the scheme's category of sheaves
  of modules over its structure sheaf.
- L is invertible: `[L.IsInvertible]`, the recorded declaration from
  WeilConjectures.AlgebraicGeometry.Modules.Invertible. Its exists_isoUnit field
  says each point has an open neighbourhood where the restriction is isomorphic
  to O_X. Local freeness of rank one also entails quasi-coherence, so the node's
  quasi-coherence clause is not an additional omitted hypothesis.
- L is ample: `(hL : Modules.IsAmple X L)`, the recorded declaration from
  Sheaf.AlgebraicGeometry.Ample. I read its body: CompactSpace X is
  quasi-compactness (no Hausdorff condition), followed by, for each point, a
  positive tensor power and a global section whose exact nonvanishing locus is
  an affine open containing the point. The germ not belonging to maximalIdeal
  times the stalk module is precisely the source's condition. This is the
  dependency's absolute ampleness, not upstream AlgebraicGeometry.IsAmple on
  projective schemes over fields. There are no hidden extra instances.
- E is any subset of points: `(E : Set X)`, with finite cardinality `(hE : E.Finite)`.
  No closedness or rationality assumption is added.
- There exists an open subset U of X: `∃ U : X.Opens`.
- U is affine: `IsAffineOpen U`; Mathlib/AffineScheme.lean defines this as
  IsAffine of the induced open subscheme, exactly the node's clause.
- E is contained in U: `E ⊆ (U : Set X)`; the conjunction contains both required
  conclusion clauses. The existential U occurs after the universally bound E.

Source: the local Stacks checkout is absent. I independently read the Stacks
01ZY page (https://stacks.math.columbia.edu/tag/01ZY) and the literal source
properties.tex at https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex,
label lemma-ample-finite-set-in-affine, statement and proof. Case (3) is exactly
this node; it assumes no field, Noetherian, separated, finite-type or proper
condition. I also read label definition-ample (01PS) in that tex: its two
conditions are exactly those in the imported definition. The surrounding
section introduces no standing restriction on X. The supplied docstring
carries all four node proof steps and their cited dependencies: open immersion
into Proj and closed boundary, finitely many standard opens avoiding the
boundary, graded prime avoidance, then the clopen intersection's closed
immersion into an affine standard open. Source and blueprint tags are present.

Edge cases: E empty is allowed by Set.Finite, with U the empty affine open;
X empty forces E empty and is not excluded by a Nonempty binder. A zero module
on a nonempty scheme cannot be invertible; on an empty scheme there is no
additional exclusion. Singleton and nonclosed points are included. No n occurs
in the theorem; the ampleness dependency correctly requires n > 0, not n = 0,
while its tensorPow handles zero as the structure sheaf. No characteristic or
base ring is fixed. Explicit arbitrary universe u is bound, and X.Modules is
locally rank one, so its sheaf-size convention excludes no invertible module
up to isomorphism. No unbound variable or universe is present.

Independent searches using vocabulary beyond the worker's searches:
- msearch.py leanfinder: `An ample line bundle gives a common affine neighborhood
  of finitely many points`: eight results, including Scheme.affineOpenCover_X,
  IsAffineOpen.exists_basicOpen_le and Proj.affineOpenCover. Their signatures
  concern one point, affine basic opens or an affine cover, not this theorem.
- msearch.py loogle: `"IsAffineOpen", Set.Finite`: two results, biSup_of_disjoint
  and biInf. They concern unions of disjoint affine opens or intersections,
  not a common affine neighbourhood of arbitrary finite sets under ampleness.
- msearch.py leansearch: `An ample invertible module on a scheme implies every
  finite subset has an affine neighbourhood`: unavailable (Internal Server
  Error); no mathematical negative verdict is inferred from that failure.
- rg across pinned Mathlib/AlgebraicGeometry, WeilConjectures/AlgebraicGeometry
  and lean/Sheaf/AlgebraicGeometry for `finite (set|subset)`, `finitely many points`,
  `affine neighbourhood`, and `affine neighborhood`: no exact theorem.
  I opened Hilbert/Curve.lean: exists_affineOpens_forall_mem_of_curve assumes
  SmoothOfRelativeDimension 1, IsProper and GeometricallyIntegral over a field,
  hence is a strict specialization. I also opened Modules/Ample.lean, whose
  relative/projective IsAmple cannot replace the absolute dependency. Other
  finite-set hits (Hilbert representability and effective descent) assume the
  affine-neighbourhood property rather than deduce it from absolute ampleness.
- rg for exists_affineOpen_of_isAmple in Mathlib, the upstream source,
  lean/Sheaf and dag/lean_names_upstream.json: no declaration-name collision.

H4/H5/H6/H8/H9 checks pass: no notion is privately copied, no definition is
introduced (hence none hollow), the sole theorem proof is sorry, the import
is used, and the header, namespace, tags and 100-character line limit agree
with the conventions. The node's lean.statement is verbatim the signature
before :=. No statement correction, missing notion, or dependency repair is
needed. scompile.py C1 lem-sc-ample-finite-set-affine on the sandbox module
completed cleanly (exit 0, 1.6 seconds), with no errors or warnings.
