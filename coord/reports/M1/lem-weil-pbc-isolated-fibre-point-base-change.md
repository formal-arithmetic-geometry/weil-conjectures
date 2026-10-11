## Worker report

The module states `AlgebraicGeometry.isolated_fiber_point_base_change` in
`lean/Sheaf/AlgebraicGeometry/IsolatedFibrePointBaseChange.lean`. The schemes `X`, `S`, and
`S'` are explicit and universe-polymorphic (`Scheme.{u}`); `f : X ⟶ S` is the morphism and
`[LocallyOfFiniteType f]` renders the locally-finite-type hypothesis. The base change is the
Mathlib pullback `pullback f g`, with `g : S' ⟶ S` and `x' : ↥(pullback f g)` a point.
The old-fibre point is `pullback.fst f g x'`, and its isolatedness is exactly
`IsOpen ({f.asFiber (pullback.fst f g x')} : Set (f.fiber (f (pullback.fst f g x'))))`.
The conclusion uses the second projection and says its corresponding singleton is open in
`(pullback.snd f g).fiber ((pullback.snd f g) x')`, exactly the isolatedness clause after
base change. The equalities `x = g'(x')`, `s' = f'(x')`, and `s = f(x) = g(s')` in the
prose are rendered by these projections and their pullback commutativity; no extra
hypothesis is introduced.

Dependencies used: `def-pc-scheme` and `def-pc-fibre-product` are rendered by
Mathlib's `AlgebraicGeometry.Scheme` and `CategoryTheory.Limits.pullback` (including
`pullback.fst` and `pullback.snd`); `def-weil-finite-type-morphism` is
`AlgebraicGeometry.LocallyOfFiniteType`; `def-pc-scheme-fibre` is
`AlgebraicGeometry.Scheme.Hom.fiber` and `Scheme.Hom.asFiber`.

Edge cases checked: the point type is the coerced underlying type `↥(pullback f g)`, so
empty schemes and fibres remain allowed; no finiteness, nonemptiness, or characteristic
assumption is added, and the universe is the same `u` for all schemes.

Searches made: the node's recorded LeanSearch, LeanFinder, Loogle, and Mathlib grep
searches found no scheme-level pointwise base-change theorem. `rg -n
"isolated.*fibre|singleton.*fiber" lean/Sheaf /home/ubuntu/weil-src-slopmaster2/WeilConjectures`
found only downstream uses and no existing declaration of this statement. The dependency
notions were confirmed at their recorded Mathlib declarations.

## Earlier second reading (a previous round; superseded)

The node and module were reread clause by clause. The locally finite type hypothesis is the
class binder `[LocallyOfFiniteType f]`; `f`, `g`, the pullback, and both projections render
the stated objects. `f.asFiber (pullback.fst f g x')` is the unique point of the old fibre
corresponding to the old point, while `(pullback.snd f g).asFiber x'` is the corresponding
new-fibre point. The two `IsOpen` singleton predicates match the hypothesis and conclusion
without added or dropped assumptions. No mismatch was found.

## Second reading by M1

I read the delivered node, its Lean module, and all four statement dependency nodes.
The literature checkout is absent on this machine, so I read the source on the server:
`morphisms.tex` lines 3660–3745 and 3920–3975, and `more-morphisms.tex` lines
12045–12090. Lemma 01TH identifies quasi-finiteness at a point with isolatedness
in the fibre under precisely the locally finite type assumption. Lemma 01TM (1)
preserves that locus under arbitrary base change, with no Noetherian, separated,
finite-type, characteristic or field hypothesis. The use in 02LM agrees.

Clause-by-clause inventory and verdict:

- Objects X and S, and morphism f: `{X S S' : Scheme.{u}} (f : X ⟶ S)`.
  PASS: `Scheme` and `Scheme.Hom` are the locally ringed spaces and morphisms of
  `def-pc-scheme` (Mathlib `Scheme.lean` lines 42 and 74).
- Hypothesis f locally of finite type: `[LocallyOfFiniteType f]`. PASS: the
  class in `Morphisms/FiniteType.lean` line 43 requires finite-type maps on affine
  open pairs, the notion recorded by `def-weil-finite-type-morphism`, not globally
  finite type. There is no quasi-compactness binder.
- Object S' and arbitrary base change g: `(g : S' ⟶ S)`. PASS: g has no
  additional property or instance assumption.
- Object X' and projections g', f': `pullback f g`, `pullback.fst f g`,
  `pullback.snd f g`. PASS: I opened `HasPullback.lean` lines 95, 111, 115;
  these are the chosen universal fibre product of `def-pc-fibre-product`.
  Scheme pullbacks exist, so no extra pullback-existence hypothesis is imposed.
- Point x': `(x' : ↥(pullback f g))`. PASS: an arbitrary underlying point.
- Introduced x, s', s and the equality f(x) = g(s'): x is substituted as
  `pullback.fst f g x'`, s' as `(pullback.snd f g) x'`, and s as
  `f (pullback.fst f g x')`. PASS: the remaining equality follows from
  `pullback.condition`; these are determined points, not extra quantified data.
- Hypothesis x isolated in X_s: `hx : IsOpen ({f.asFiber (pullback.fst f g x')} :
  Set (f.fiber (f (pullback.fst f g x'))))`. PASS: I opened `Fiber.lean`
  lines 38, 103, 116, 120. `fiber` is the pullback with Spec of the residue
  field as recorded by `def-pc-scheme-fibre`; `asFiber` is the inverse of
  `fiberHomeo` at x and its projection is x. This is exactly the open singleton
  in the scheme-theoretic fibre, not a chosen lift or geometric fibre.
- Conclusion x' isolated in X'_{s'}: `IsOpen ({(pullback.snd f g).asFiber x'} :
  Set ((pullback.snd f g).fiber ((pullback.snd f g) x')))`. PASS: the same
  scheme-theoretic fibre construction for f' and its uniquely corresponding
  fibre point. All objects precede the isolatedness hypothesis and conclusion.

Edge cases: empty schemes and empty pullbacks are allowed, with the universally
quantified point making those cases vacuous. Fibres at the chosen image points
contain the corresponding `asFiber` point without a nonempty assumption. There is
no index set, n, module, or zero-object parameter. No characteristic or residue
field restriction occurs. The universe u is declared and arbitrary; the common
scheme universe is Mathlib's category of schemes at any size, and may be enlarged
to contain any finite collection of schemes. No independent smaller testing
universe, unbound variable, or extra ring structure occurs.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanSearch: "An open singleton in a scheme fibre remains open in the fibre
  after extending the base scheme". The service returned Internal Server Error;
  no negative result is claimed for that unavailable search.
- Loogle: `AlgebraicGeometry.Scheme.Hom.asFiber, IsOpen`. One hit:
  `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`, which I opened in
  `Morphisms/QuasiFinite.lean` lines 395–440. It characterizes isolatedness but
  does not assert pointwise base-change preservation.
- LeanFinder: "Isolated points in fibres of locally finite type scheme morphisms
  are preserved by arbitrary base change". Eight hits: stability of locally
  finite type, finite and globally locally quasi-finite morphisms, projection
  instances, finite fibres and discrete finite fibres. None is this pointwise
  statement; the global quasi-finite instance assumes every point is quasi-finite.
- Mathlib grep: `asFiber|quasiFiniteAt.*base|isolated.*fiber` in AlgebraicGeometry.
  It found fibre definitions and the same characterization/clopen-singleton
  consequences, but no pointwise base-change theorem.
- Independent rg over project `lean/Sheaf` and source `WeilConjectures` for
  `isolated_fiber_point_base_change|singleton.*(fiber|pullback)|[Qq]uasiFiniteAt.*(baseChange|pullback)|isolated.*(fibre|fiber)`:
  neighbouring étale-local lemmas and unrelated finite-fibre results only.
  No duplicate of this statement or private definition was found.

Mismatch found and repaired: H8. The previous docstring compressed four proof
steps into a short paragraph and omitted the locally finite type argument for the
open singleton scheme and the named dependency nodes. I expanded it to all four
node proof steps with their dependency identifiers and explicit source places
01TM, 01TH, and the proof of 00PP. The Lean signature is unchanged; the node's
`lean.statement` is now the verbatim multiline signature from the module.
No mathematical statement correction, new definition node, or dependency module
is needed. Both imports serve notions in the signature. There is only one theorem,
its proof remains `sorry`, no definitions or data holes are introduced, and all
lines of the module are at most 100 characters.

Validation: scompile.py compiled the 49-line module on the server in 1.6 seconds,
exit code 0, with no warnings. The deliver2.py dry run printed OK: preflight and
compilation passed. I also opened the global locally-quasi-finite base-change
instances in Mathlib `Morphisms/QuasiFinite.lean` lines 115–126 to confirm that
they require the stronger global hypothesis and cannot replace this statement.
