## Worker report

Repair of the returned stage-2 head 45d5d59f833f. At the start of this retry the
sandbox contained dispatcher marker files and no retained module/node/report.
The node was therefore copied afresh from the current shared live DAG, including
its reviewed 20-step proof and split_report. Only its lean field is changed.
In particular this delivery makes no stage-1 edits to proof steps 6/13/15 or to
split_report; the NE stage-1 landing is preserved.

Module: lean/Sheaf/Paper/StrictLocalPrimeToPKummerSplitting.lean.
Main declaration: AlgebraicGeometry.strictLocalPrimeToPKummerSplitting.
It is a theorem with proof sorry. Four auxiliary constructions, all recorded in
lean.declarations, give the literal simultaneous-root quotient, original
puncture, root-level puncture, and canonical map of punctures. These are the
objects already displayed in this node, not new independent mathematical
notions. Their data are real Mathlib constructions, with no postponed data or
choice of an unspecified map. There are no other postponed theorems.

Source read: ILO Travaux de Gabber, Expose IX, Proposition 2.1(i), printed
pp.133–134 (PDF pages 139–140). Its proof reduces to a strictly local regular
ring with boundary parameters, gives the displayed simultaneous root quotient
and describes each connected tame cover as a quotient of it. The node is the
stated finite prime-to-p-group consequence, permitting a disjoint union of
connected components; it does not assert tameness from the degree alone.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| p prime | `p : ℕ`, `hp : p.Prime` |
| R commutative, Noetherian regular local | `R : Type u`, `[CommRing R]`, `[IsRegularLocalRing R]`; the latter extends both `IsLocalRing` and `IsNoetherianRing` |
| characteristic p | `[CharP R p]` |
| strictly henselian, henselian with separably closed residue field | upstream `[IsStrictlyHenselianLocalRing R]` |
| r ≥ 0, including zero | `r : ℕ`, with no positivity assumption |
| the selected ordered parameters t_1,…,t_r | `t : Fin r → R`, with Lean indexing starting at zero |
| distinct members | `ht : Function.Injective t` |
| members of a regular system of parameters | `hparams : ∃ s : List R, IsLocalRing.IsRegularSystemOfParameters s ∧ ∀ i : Fin r, t i ∈ s`; the same full system contains every selected member |
| f is their product, empty product 1 | `∏ i, t i`, the product over `Fin r` |
| U = Spec R[1/f] | `strictLocalBoundaryPuncture t`, defined literally using `Spec` and `Localization.Away` |
| finite group G, p does not divide its order | `G : Type v`, `[Group G]`, `[Finite G]`, `hG : ¬ p ∣ Nat.card G` |
| P → U finite, etale, surjective, G acting over U and simply transitively on geometric fibres | `P : Scheme.GaloisCoverAction G (strictLocalBoundaryPuncture t)`; its fields are `Z`, `π`, `isFinite`, `etale`, `surjective`, `smul`, `smul_π`, `one_smul`, `mul_smul`, `simply_transitive`, and the equivalent quotient property |
| no connectedness assumption on P | no `IsConnected`, `IsIntegral`, `PreconnectedSpace`, or analogous binder |
| exists integer n ≥ 1 prime to p | `∃ n : ℕ, 1 ≤ n ∧ Nat.Coprime n p ∧ …`; positive natural numbers encode precisely these integers |
| R_n = R[x_i]/(x_i^n−t_i) | `strictLocalParameterRootRing t n`, exactly `MvPolynomial (Fin r) R ⧸ Ideal.span (Set.range (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))` |
| U_n = Spec R_n[1/f] | `strictLocalParameterRootPuncture t n`, using `Localization.Away` at the image of the original product under `algebraMap` |
| the displayed R-algebra structure induces U_n → U | `strictLocalParameterRootMap t n`; it is `Spec.map` of `IsLocalization.Away.map` applied to the canonical quotient algebra map |
| actual base change P ×_U U_n | `pullback P.π (strictLocalParameterRootMap t n)` |
| coproduct of G copies of U_n | `∐ fun _ : G ↦ strictLocalParameterRootPuncture t n` |
| isomorphic over U_n to the trivial torsor | the existential scheme isomorphism `e` and equation `e.hom ≫ pullback.snd … = Sigma.desc (fun _ ↦ 𝟙 …)` |
| regular G-action and equivariant trivialization | for every `g h : G`, the `g`-component of `e.hom`, followed by the first pullback projection and `P.smul h`, equals the `(h * g)`-component followed by that projection |
| r = 0 has n = 1 | the same witness satisfies `(r = 0 → n = 1)` |

The isomorphism is oriented from the trivial torsor to the pullback, as in proof
steps 18–19; its inverse is the requested trivialization. The equivariance
formula is an exact expression of the pulled-back action without choosing an
arbitrary action map: the first pullback projection intertwines the given
P-action by the displayed formula, and the second projection intertwines the
identity on the base by the over-base equation. Pullback uniqueness gives the
full action equality. Equality on coproduct components gives the equality of
maps for the left regular action g ↦ h*g. Thus this is equivariance of schemes,
not merely a bijection on geometric points.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: its docstring and full definition
  identify the node's ring clauses with Mathlib `IsRegularLocalRing` and
  `IsRegularRing`. The statement uses the former, whose signature in
  `Mathlib/RingTheory/RegularLocalRing/Defs.lean:51` was also read.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing` (lines 121 onward) extends `HenselianLocalRing`
  with `isSepClosed_residueField`; the equivalence immediately below was read.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, the equality of the generated ideal
  with `maximalIdeal` and of list length with `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` (lines 470/479).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away` (line 142),
  with the ring construction and `IsLocalization.Away.map` from
  `Mathlib.RingTheory.Localization.Away.Basic` (line 203). The latter is exactly
  the induced map of the two displayed localizations.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite` (line 39);
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (line 41);
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective` (line 59).
  These are the structure fields of the recorded cover interface, publicly
  available through its module, not private redefinitions.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`:
  `Scheme.GaloisCoverAction`, read in full including its docstring and geometric
  test-field universes. It accepts `G : Type v` independently of `Scheme.{u}`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` (line 82), `X`, and `C`.
  The recorded evaluation/uniqueness interface was also read in Basic and Eval;
  the theorem needs the actual polynomial-ring presentation.

All already-recorded Lean proof dependencies are imported with plain `import`.
Statement interfaces are public imports. No definition or theorem belonging to
a dependency node is copied or repaired here.

Edge cases checked: `r = 0` has `Fin 0` empty, product one, a polynomial ring
with no variables and the zero relation ideal. Its quotient is canonically R,
and localization away from one is canonically R. These are canonical
isomorphisms rather than definitional equalities, so the theorem keeps the
literal presentation and asks for n = 1. For dimension zero the full regular
parameter list can be empty. A nonzero-dimensional R with r = 0 is also covered:
the chosen sublist is empty while hparams allows a nonempty full list. The
trivial group has order one and no excluded case. Disconnected P is allowed by
the exact recorded structure, without any connectedness field. Universes u and
v are independent; finiteness supplies Small for the coproduct, so no group
universe equality or additional smallness hypothesis was introduced. The zero
ring is excluded by the existing local-ring notion, as in the source.

Searches actually run through msearch.py for this group and item:

- LeanFinder: "A torsor with finite prime-to-characteristic group over a strictly
  henselian regular local ring punctured along parameters is trivialized by
  adjoining roots of the parameters". Eight hits (HenselianLocalRing, its TFAE,
  Field.henselian, StandardEtalePair, PreTilt and related declarations), none
  states the splitting theorem.
- Loogle: `Scheme.GaloisCoverAction, Localization.Away, MvPolynomial`.
  Service answered zero hits and unknown identifier `Scheme.GaloisCoverAction`;
  this query did not establish the absence of the upstream interface, which was
  located and read directly as recorded in the node.
- grep: `Kummer|kummer|GaloisCover`, subdirectory AlgebraicGeometry. Zero hits.
- LeanSearch: "finite etale torsor strictly henselian regular local parameter
  roots splitting". Eight hits: HenselianLocalRing.TFAE,
  Algebra.FormallyEtale.iff_exists_algEquiv_prod, Polynomial.rootOfSplits',
  Algebra.FormallyEtale.iff_isSeparable and its auxiliary, HenselianLocalRing
  constructors, and Field.henselian. None is the splitting statement.
- `rg` of the read-only `lean/WeilConjectures` and `lean/Sheaf` for Kummer,
  kummer, simultaneous roots, root algebras and root rings: field-theoretic
  Kummer and Tate-twist results were not this statement. Exact node-id grep in
  WeilConjectures gave no hit. Exact proposed declaration-name searches in
  Mathlib, WeilConjectures and Sheaf gave no collision.
- DAG search for simultaneous roots and parameter-root definitions found
  `def-sfb-full-parameter-root-tower` and its underlying
  `def-sfb-strict-local-kummer-tame-module`. Their Lean declarations were read:
  they define the infinite compatible-root algebra with transition relations
  for all prime-to-p orders, not this finite-level polynomial quotient.
  No duplicate of that infinite tower is introduced.
- `tools/blueprint_refs.py search strict root` returned 13 blueprint nodes;
  none states this finite prime-to-p torsor splitting result.

No statement correction, disputed statement, new DAG node or dependency module
is needed. The complete live proof is included, numbered step by step, in the
main theorem docstring. The node's Lean signature is copied verbatim from that
file, and every auxiliary declaration is listed in lean.declarations.

Validation: scompile.py compiled both the sandbox check and actual module cleanly
on the server. The initial compiler request identified that the two Spec-valued
helper definitions require `noncomputable`; both were corrected and the next
compile was clean. No local compiler or global build was used.

## Second reading by NJ

This is a second pass by the directly dispatched NJ worker, not an independent
worker review; the dispatcher forbids starting agents and the maintainer supplies
the independent reading. With the node, file, recorded dependency signatures and
ILO pp.133–134 open, this pass checked the table above against the actual final
signature. In particular the theorem includes both regularity and strict
henselianity, characteristic p and primality of p, distinct selected parameters
inside one full regular system, a finite group with order prime to p, and the
finite etale surjective geometric-fibre torsor structure without connectedness.
The finite-root quotient has one variable and relation per selected parameter;
the puncture inverts the image of exactly the original product. The base-change
map is the localization of the canonical quotient R-algebra map. The resulting
isomorphism has the explicit over-U_n equation and the left-regular action
formula on every component. The r = 0 implication fixes the positive coprime
witness to 1 without imposing r > 0 elsewhere. No mismatch was found in this
pass; the compiler-driven noncomputable markings change no mathematical data.

Return repair accounting: H1 is repaired by the actual Lean module, lean record,
and both required report sections. H2 is repaired by copying the current live
node and changing only lean: no old proof/split_report edits survive. H11 is
repaired by this explicit reading of every hypothesis and conclusion clause,
including disconnected P, r = 0, the root-level map, the base equation and
G-equivariance. No claim of a separate worker's review is made.
