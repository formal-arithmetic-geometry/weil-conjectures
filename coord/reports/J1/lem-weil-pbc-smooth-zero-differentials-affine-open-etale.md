## Worker report

The module states that a smooth morphism `g : U ⟶ S`, restricted along affine opens `W ≤ g ⁻¹ᵁ V`, is étale when the Kähler differential module of the induced section ring map is subsingleton. The hypotheses are rendered by `{U S : Scheme.{u}}`, `(g : U ⟶ S) [Smooth g]`, opens `V W`, affine-open proofs `hV hW`, and containment `hWV`. The differential clause is `Subsingleton (@KaehlerDifferential _ _ _ _ ((g.appLE V W hWV).hom.toAlgebra))`; the conclusion is `Etale (W.ι ≫ g)`. The proof is `sorry`, as required for a stage-2 statement.

Dependencies used are Mathlib's `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Smooth`, `AlgebraicGeometry.Etale`, and `KaehlerDifferential`; these are imported directly. The induced algebra structure is explicitly the one from `(g.appLE V W hWV).hom.toAlgebra`, avoiding an unbound algebra instance. Empty opens and zero differential modules are covered by the unrestricted affine-open and `Subsingleton` hypotheses.

Searches: `rg` over `lean/Sheaf` and the slopmaster2 source for smooth, étale, affine-open, and Kähler differential statements found no matching whole theorem; Mathlib search identified only component notions (`Smooth`, `Etale`, `KaehlerDifferential`), so a new statement module was needed.

## Earlier second reading (a previous round; superseded)

The Lean signature matches the node's objects and clauses: smoothness of `g`, affine opens `V,W` with `g(W) ⊆ V`, vanishing differentials expressed as subsingleton, and étaleness of the restriction to `S` via `W.ι ≫ g`.

## Second reading by J1

I independently opened the item, all five statement-dependency nodes and their recorded
Mathlib declarations, the sandbox module, and the cited Stacks source on the server
(the literature checkout is absent on this machine). No statement correction is needed.
There are no new definition nodes or dependency modules in this delivery.

Object/hypothesis/conclusion inventory, matched in statement order:

- Arbitrary schemes U and S (`def-pc-scheme`): `{U S : Scheme.{u}}`.
  Mathlib Scheme extends LocallyRingedSpace with local affine charts; its category morphisms
  are the node's scheme morphisms. Verdict: exact.
- Morphism g : U → S: `(g : U ⟶ S)`. Verdict: exact, no over-base structure added.
- Smoothness (`def-sbc-smooth-morphisms`): `[Smooth g]`, the dependency's recorded class
  in Mathlib.AlgebraicGeometry.Morphisms.Smooth. Its field smooth_appLE tests the induced
  maps on all affine opens. Stacks 01V6 identifies this with smoothness; 02H6 identifies
  smoothness with locally finite presentation plus formal smoothness, as the dependency
  states. Verdict: exact; no Noetherian, separated, field or quasi-compact assumption.
- Affine open V ⊆ S: `(V : S.Opens) (hV : IsAffineOpen V)`.
  Affine open W ⊆ U: `(W : U.Opens) (hW : IsAffineOpen W)`.
  IsAffineOpen is IsAffine of the open subscheme, i.e. an isomorphism to a spectrum of
  a commutative ring, agreeing with `def-weil-affine-spectrum` and `def-pc-scheme`.
  Verdict: exact; neither open is required to be nonempty or to contain a chosen point.
- Containment g(W) ⊆ V: `(hWV : W ≤ g ⁻¹ᵁ V)`.
  The inverse-image open uses the underlying map of g. Verdict: equivalent containment.
- R = O_S(V), A = O_U(W), with their specific induced ring map:
  `g.appLE V W hWV : Γ(S,V) ⟶ Γ(U,W)` and its `.hom.toAlgebra`.
  Scheme.Hom.appLE is g.app V followed by restriction to W, exactly the node's map.
  R and A are inferred from that map in `@KaehlerDifferential _ _ _ _ ...`;
  they are not arbitrary algebras or separately quantified rings. Verdict: exact.
- Ω_A/R = 0 (`def-weil-pbc-kahler-differentials`):
  `(hΩ : Subsingleton (@KaehlerDifferential _ _ _ _
    ((g.appLE V W hWV).hom.toAlgebra)))`.
  Opened KaehlerDifferential and linearMapEquivDerivation in Kaehler.Basic: the latter
  identifies A-linear maps with R-derivations, the node's universal property.
  Subsingleton of this additive module means every element equals zero, including for
  the zero ring; it expresses vanishing, not IsZero of an unbundled Type. Verdict: exact.
- Conclusion, the restriction W → S is étale (`def-weil-etale-morphism`):
  `Etale (W.ι ≫ g)`. The composite has source W.toScheme and target S, not just V.
  Opened Etale's affine-local field and iff_flat_and_formallyUnramified: the recorded
  notion agrees with the dependency's flat, unramified and locally finitely presented
  definition (Stacks 02GI/02GV/02GE). Verdict: exact, with one conclusion clause.

Source check: read morphisms.tex around 01V5/01V6 and 02GH/02GI and the full statements
of 02GN and 02GP, plus more-morphisms.tex 02H6, over SSH. They apply to arbitrary schemes;
01V6 and the discussion after 02GI explicitly require neither separation nor
quasi-compactness. The sentence before 02GI defines an étale ring map by smoothness and
zero differentials. No standing characteristic, finiteness of the base, or field
hypothesis is missing. The five-step node proof correctly transports the affine map
through the canonical spectrum identifications and composes with V → S.

Edge cases: empty U or S and empty affine W or V remain permitted. The empty affine
scheme is the spectrum of the zero ring, and no Nontrivial/Nonempty instance occurs.
The differential module may be zero. All characteristics and general commutative
section rings are allowed. There is no index set or integer n in this statement, so
empty indexing and n = 0 add no excluded case. The arbitrary universe u is bound;
both schemes are objects of the same category Scheme.{u}, as are their opens, with
no independently smaller universe of test objects and no unbound variables.

Independent searches (2026-10-11), using msearch.py to record actual queries:

- LeanSearch: “A smooth morphism restricted to affine open subschemes is etale if the
  module of relative differentials vanishes”. Service returned Internal Server Error;
  unavailable, so no conclusion is drawn from this search.
- Loogle: `"Etale", "appLE"`. Two hits, Etale.etale_appLE and its Scheme.Hom alias;
  both assume étaleness and conclude ring-map étaleness, not this theorem.
- LeanFinder: “Smooth scheme morphism with zero relative Kahler differentials on an
  affine chart is etale on that chart”. Hits include the reverse étale-to-smooth
  instance, RingHom.etale_iff_formallyUnramified_and_smooth, and standard-smooth
  relative-dimension-zero algebra instances. These are components, not the statement.
- Mathlib grep: `etale.*(differential|subsingleton)|differential.*etale|etale.*appLE`.
  Hits are ring differential base-change facts and the étale appLE fields.
- Independently ran the same expression and the full declaration name over
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json. The finite-algebra-over-a-field differential criterion
  and the group-scheme criterion specialize the objects and do not cover this node.
  The smooth-zero-fibre-dimension module cites this node; it does not state its theorem.
  No existing whole declaration found. All notions already have usable recorded
  dependencies, so no private copy or extra node is needed.

Mismatch and repair: the original theorem docstring compressed the proof into one
paragraph and omitted explicit factorization uniqueness, transport across both affine
isomorphisms, and the five dependency-labelled steps (H8). Replaced that paragraph
with all five steps and their node references. The mathematical signature, imports,
node statement, dependencies and recorded lean.statement remain unchanged and correct.
No definitions or proofs were added; the sole theorem retains `by sorry`.
Checked the signature verbatim against lean.statement and all Lean line lengths ≤ 100.
Server single-file compile via scompile.py succeeded in 1.7 seconds with no warnings.
