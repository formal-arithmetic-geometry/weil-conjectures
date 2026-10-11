## Worker report

The module `lean/Sheaf/AlgebraicGeometry/Curve/ProperCohomology.lean` states
`AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isProper`, with one `sorry`
and no definitions or proofs. The node copy changes only `lean`.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The curve over this field is `{C : Scheme.{u}}` with structure morphism
  `(f : C ⟶ Spec (.of k))` and `[IsConnectedCurve f]`. The recorded curve module's
  class extends `IsCurve f`, supplying separatedness, finite type and dimension at
  most one; it additionally requires connectedness, nonemptiness and dimension one.
- Smoothness is `[Smooth f]` and properness is `[IsProper f]`.
- Genus is the existing `f.genus`, so the named `g` is substituted by its definition,
  the dimension over k of global differential forms. This does not quantify over
  an unrelated number or add a genus hypothesis.
- The natural number n is `(n : ℕ)` and invertibility is `(hn : (n : k) ≠ 0)`.
  For a field this is precisely invertibility of n; it implies n >= 1 and being
  prime to the characteristic (including characteristic zero).
- The constant sheaf F_n is exactly `C.constantZMod n`, the sheafification of the
  constant presheaf with value `ULift (ZMod n)` on `C.smallEtaleTopology`.
- `H^0 ≅ Z/n` is `Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n)`.
- `H^1 ≅ (Z/n)^(2g)` is the second conjunct, an additive equivalence with
  `(Fin (2 * f.genus) → ZMod n)`.
- `H^2 ≅ Z/n` is the third conjunct, with degree 2.
- Vanishing for EVERY q > 2 is
  `∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H (C.constantZMod n) q)`.
  These are abelian groups, so subsingleton means the zero group.
- The primitive-root trivialization is the method of identification, not an extra
  conclusion asserting a specific numerical isomorphism. The node gives no formula
  for the three displayed group isomorphisms, and the Picard torsion basis is also
  noncanonical. Thus `Nonempty` preserves exactly its existence assertions, as in
  Stacks 03RQ and the upstream degree-one/two statements. The docstring explicitly
  specifies the existing theta_zeta sheaf isomorphism and transports along it;
  choosing the root is justified by the recorded primitive-root theorem, rather
  than imposed as an additional hypothesis.

Dependencies read and reused:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`,
  `AlgebraicGeometry.IsConnectedCurve`, `AlgebraicGeometry.Scheme.Hom.genus`.
  Full definitions and docstrings were read. The connected specialization is in
  the same recorded module and supplies exactly the node's connected-curve notion.
- `WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`:
  `AlgebraicGeometry.Scheme.constantZModToRootsOfUnitySheaf`,
  `AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf`, and
  `AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`.
  Their full signatures and docstrings were read. The last is the canonical map
  a ↦ zeta^a for a primitive root. The imported module supplies the constant sheaf
  via `WeilConjectures.AlgebraicGeometry.Sites.Kummer`.
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`:
  `IsSepClosed.exists_isPrimitiveRoot`; also read
  `IsPrimitiveRoot.zmodAddEquivRootsOfUnity` in
  `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`.
  These are used in the natural-language proof, not as extra assumptions or
  private replacement definitions. Their imports will be needed in stage 3.
- Mathlib `CategoryTheory.Sheaf.H` in
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` is the existing abelian-sheaf
  Ext cohomology. Its full definition and docstring were read; the upstream
  constant-sheaf calculations use the same cohomology and supplied instances.

Edge cases checked before writing: n = 0 is excluded by hn; n = 1 gives trivial
coefficient and cohomology groups and remains allowed. In characteristic zero
all positive n are allowed, and in positive characteristic exactly the invertible
ones are allowed. Genus zero gives the empty Fin 0 product in degree one, hence
zero. Empty schemes, disconnected schemes and Spec k are correctly excluded by
IsConnectedCurve, whose dimension-one clause is essential for degree two when
n > 1. The statement does not require n prime. Arbitrary scheme/field universes
are included by the explicit universe u, matching the recorded upstream encoding;
there is no new test-object universe or unbound variable.

Searches (all through the prescribed tooling or direct read-only searches):

- `msearch.py ... leanfinder`: query "Etale cohomology of a smooth proper connected
  curve over an algebraically closed field with constant Z/n coefficients H0 H1
  H2 genus and vanishing above degree two". Eight hits, only cotangent, group or
  singular cohomology; no match.
- `msearch.py ... loogle`: query `Sheaf.H, ZMod`. Zero hits; unknown identifier
  `Sheaf.H` in that service's index.
- `msearch.py ... leansearch`: query "Etale cohomology smooth proper connected
  curve constant ZMod n genus". Service unavailable: Internal Server Error.
- `msearch.py ... grep`: query `constantZMod|sheafH.*genus|proper.*cohomology`
  under Mathlib `AlgebraicGeometry`. Zero hits.
- `rg` of the source `WeilConjectures/` found the three separate degree statements
  in `AlgebraicGeometry/Curve/Estimate.lean`; read each signature and docstring.
  No declaration there states their conjunction together with higher vanishing.
  `Curve/CohomologicalDimension.lean` has the separate higher-vanishing input.
- `rg` of project `lean/Sheaf/`, source `WeilConjectures/`, and
  `dag/lean_names_upstream.json` for `thm-sc-proper-cohomology`,
  `proper_cohomology`, and `sheafH_constantZMod_of_isProper`: no hits.
  The required source tag search likewise found no exact node-tag attachment.
- Broad source searches for `constantZMod`, `Sheaf.H`, genus and curve cohomology
  found the existing notions above. No new notion, node or dependency module is
  needed, and the theorem's full qualified name has no collision.

Source check: the local literature files are absent on this remote machine.
Opened https://stacks.math.columbia.edu/tag/03RQ directly: its statement and proof
confirm all four constant-sheaf cohomology clauses and the noncanonical nature of
these identifications. Its projective-curve form applies here since smooth proper
connected curves over a field are projective. The node's proof steps are copied
faithfully into the declaration docstring with every dependency named.

No statement correction, disputed statement, or dependency fault was found.
Server validation: `scompile.py E1 thm-sc-proper-cohomology` compiled the module
in 2.1 seconds with exit code 0 and no warnings or errors. The required dry run
is recorded below after completion.

Dry run: `deliver2.py E1 thm-sc-proper-cohomology --no-push` printed OK:
the generated commit compiles and passes preflight except for the independent
second reading, which the second reader must write. Nothing was pushed.

## Second reading by E1

I independently opened the node `thm-sc-proper-cohomology`, its three statement dependencies, and
`lean/Sheaf/AlgebraicGeometry/Curve/ProperCohomology.lean`. The item-by-item correspondence is:

- The algebraically closed base field is rendered by `{k : Type u} [Field k] [IsAlgClosed k]`.
- The curve and its structure map are rendered by `{C : Scheme.{u}}` and
  `f : C ⟶ Spec (.of k)`. The instance `[IsConnectedCurve f]` is the recorded
  connected-curve notion: it extends `IsCurve f` (separated, locally of finite type,
  quasi-compact, dimension at most one), and supplies connectedness and dimension one.
- Smoothness and properness are exactly `[Smooth f]` and `[IsProper f]`; no extra
  separatedness, finiteness, or Noetherian hypothesis is introduced.
- The source's genus `g` is rendered by `f.genus`, the recorded `Scheme.Hom.genus`.
- The coefficient integer is `(n : ℕ)`, with `(hn : (n : k) ≠ 0)`. Over a field this is
  exactly invertibility of `n`, hence implies `n ≥ 1` and prime-to-characteristic; no
  primality assumption is added.
- The constant sheaf is exactly `C.constantZMod n`, the recorded constant sheaf used by
  the roots-of-unity trivialization.
- The four conclusion clauses are rendered in the same order: `Nonempty` additive
  equivalences in degrees 0, 1 (with `Fin (2 * f.genus) → ZMod n`), and 2, followed by
  `∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H (C.constantZMod n) q)`. For these abelian
  groups, `Subsingleton` is the zero-group assertion, matching vanishing for every `q > 2`.
  The primitive-root trivialization is proof data for the noncanonical identifications,
  not an additional numerical clause in the node.

Edge cases were checked: `hn` excludes `n = 0` while allowing `n = 1`; characteristic zero
allows every positive `n`, and positive characteristic allows exactly the nonzero casts;
genus zero gives the empty `Fin 0` product in degree one; the connected-curve instance
excludes empty, disconnected, and zero-dimensional schemes; no independent test-object
universe is introduced. The explicit common universe `u` covers the node's scheme/field
cases.

I searched the pinned Mathlib, the slopmaster2 source, and project `lean/Sheaf` with the
LeanSearch/Loogle/LeanFinder queries and `rg` searches recorded in the worker report. The
only matching notions are the existing `Sheaf.H`, `IsConnectedCurve`, `Scheme.Hom.genus`,
constant-sheaf roots-of-unity map, and primitive-root declarations; no declaration states
this conjunction. The dependency declarations were read at their source signatures and
are used by the module's proof docstring. The Stacks source place (Tag 03RQ, with vanishing
from 03RT) matches all four clauses.

No mismatch was found, so no source, node, statement, dependency, or Lean change was needed.
The module has exactly one named theorem and one permitted `sorry`; its declaration and
module docstrings identify Tag 03RQ and `(blueprint: thm-sc-proper-cohomology)` and record
the proof steps. The required single-file compile completed cleanly.

Independent search details: Loogle `ZMod, _ ≃+ _` found cyclic-group equivalences only;
LeanFinder "cohomology groups of a nonsingular complete algebraic curve with cyclic finite
constant coefficients vanish in degrees above two" returned eight unrelated group/singular
cohomology hits. LeanSearch "cohomology of complete nonsingular curves cyclic coefficients
degree two" was unavailable (Internal Server Error). Direct `rg` for
`sheafH_constantZMod|constantZMod.*genus|Subsingleton.*Sheaf.H` in Mathlib algebraic geometry,
project Sheaf, and source curve modules found the separate upstream degree calculations and
vanishing statements, not the complete conjunction. I read `Curve/Estimate.lean` lines 55–108
and the dependency signatures in `Sites/RootsOfUnity.lean` and
`Mathlib/RingTheory/RootsOfUnity/AlgebraicallyClosed.lean`. The Stacks `.tex` was downloaded to
sandbox scratch `.source-etale.tex`; lines 11135–11216 give the source statement and proof.
It assumes smooth projective curves; smooth proper connected curves over a field are
projective, so this changes no hypothesis. No delivery definition nodes or dependency modules
exist to audit, and the item has no `statement_change` requiring citer revalidation.
