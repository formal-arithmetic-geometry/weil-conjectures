## Worker report

The module `Sheaf.AlgebraicGeometry.NormalCurveUniversalClosednessTest` states
`AlgebraicGeometry.normal_curve_universal_closedness_test`. Its only theorem has
proof `sorry`; no new notion or helper theorem is introduced. The node is copied
with only its `lean` field added. Its accepted split and mathematical statement
are preserved.

Source checked: `literature/stacks-project/limits.tex`, Tag 0GWV, label
`lemma-essentially-finite-type-criterion-universally-closed`, including the full
three-condition statement and its proof. Over Spec k the Nagata hypothesis holds
by Tag 0335. The statement deliberately asks for a local lift, without uniqueness
or extension over all C.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| k is any field | `(k : Type u) [Field k]` |
| X and Y are k-schemes | `X Y : Scheme.{u}` with structure maps `p`, `q` to `Spec (CommRingCat.of k)` |
| Both are locally of finite type over k | `[LocallyOfFiniteType p] [LocallyOfFiniteType q]` |
| g is a quasi-compact k-morphism | `(g : X ⟶ Y) [QuasiCompact g] (hg : g ≫ q = p)` |
| Three conditions are equivalent | `List.TFAE` on the three displayed propositions |
| (1) Universal closedness | `UniversallyClosed g` |
| (2) Every integer n at least zero | `∀ n : ℕ` |
| Affine n-space with exactly its usual structure map | `Spec (CommRingCat.of (MvPolynomial (Fin n) k))`, with `Spec.map (CommRingCat.ofHom MvPolynomial.C)` |
| Products over k and the morphism 1 × g | `pullback.map` with factors the affine-space structure map and `p`/`q`, component maps `𝟙 _`, `g`, and base map `𝟙 _` |
| The product morphism is topologically closed | `IsClosedMap` of that actual scheme morphism |
| (3) Any integral finite-type k-scheme C | `∀ (C : Scheme.{u}) (s : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [LocallyOfFiniteType s] [QuasiCompact s]` |
| All local rings are integrally closed domains | `∀ z : C, IsDomain (C.presheaf.stalk z) ∧ IsIntegrallyClosed (C.presheaf.stalk z)` |
| c is closed and its local ring has dimension one | `IsClosed ({c} : Set C)` and `ringKrullDim (C.presheaf.stalk c) = 1` |
| U is the complement of c | `∀ (U : C.Opens), (U : Set C) = {c}ᶜ → ...` |
| a and b are the specified k-morphisms | `a : U.toScheme ⟶ X`, `b : C ⟶ Y`, with `a ≫ p = U.ι ≫ s` and `b ≫ q = s` |
| The punctured square commutes | `a ≫ g = U.ι ≫ b` |
| R is the actual local ring and F its fraction field | `C.presheaf.stalk c` and `FractionRing (C.presheaf.stalk c)` |
| The required k-morphism h exists | `∃ h : Spec (C.presheaf.stalk c) ⟶ X`, with `h ≫ p = C.fromSpecStalk c ≫ s` |
| gh equals b restricted to the local spectrum | `h ≫ g = C.fromSpecStalk c ≫ b` |
| The generic restrictions agree | The final equality, pulled back to `pullback U.ι (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ C.fromSpecStalk c)` |
| No uniqueness, separatedness, or reducedness hypotheses on g,X,Y | None appears among the binders or conclusions |

Explanation of the last clause: put i = Spec(R → Frac R), and γ = i ≫ C.fromSpecStalk c.
The fibre product P = U ×_C Spec F has its two existing canonical projections.
The equality is `P.snd ≫ i ≫ h = P.fst ≫ a`. Since C is integral, γ maps to its
generic point. The assumption dim R = 1 ensures that point is not c, so γ lands
in U and P.snd is an isomorphism. Hence the equality is exactly agreement on all
of Spec F. It neither chooses an arbitrary generic map nor assumes a separate
factorization; it uses the canonical restriction construction. Quantifying over
an open U with the specified underlying set introduces no extra condition:
closedness of c supplies exactly one such open, and opens with the same set are
equal. Likewise the h-over-k equation is the node's k-morphism requirement (it
also follows from the square and the other over-k equations).

Dependency interfaces read and used:

- `Field` from `Mathlib.Algebra.Field.Defs` (through the public scheme imports).
- `AlgebraicGeometry.Scheme` and `Spec`/`Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `LocallyOfFiniteType` and `QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `UniversallyClosed`, recorded together with `IsProper`, through
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `IsIntegral` from `Mathlib.AlgebraicGeometry.Properties`.
- `IsIntegrallyClosed` (and the standard `IsDomain`) from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
- `ringKrullDim` from `Mathlib.RingTheory.KrullDimension.Basic`.
- `MvPolynomial` and `MvPolynomial.C` from `Mathlib.Algebra.MvPolynomial.Basic`.
- `pullback`, its two projections and `pullback.map` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; the scheme
  pullbacks instance from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Scheme.fromSpecStalk` from Mathlib's Stalk module, used through the recorded
  `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`, whose
  `Scheme.fromSpecStalk_local_properties` gives the required canonical map and
  properties. Its full signature and docstring were read.

The stated proof dependencies are imported privately (the statement dependencies
are public). These include the recorded upstream reduced-induced-closed-subscheme
module and Regular module, plus the Mathlib closed-immersion, finite-type,
Noetherian, localization and valuative modules. The following proof dependencies
have no recorded declaration at delivery preparation and therefore have no module
to import: `lem-sfb-missing-fibre-finite-presentation-approximation`,
`lem-sfb-finite-type-image-immediate-boundary-point`,
`lem-sfb-normal-curve-punctured-generic-model`. They are not prerequisites for
stating the item; their proof steps remain in its docstring.

Edge cases checked before writing: n = 0 is included (MvPolynomial on Fin 0 gives
Spec k); empty X or Y is not excluded and condition (3) remains correctly
quantified; no reducedness or separatedness assumption has been inserted. An
integral zero-dimensional C or a field local ring is excluded only by the source's
explicit dimension-one test. All field characteristics are allowed. The local
fraction field and test schemes live in the same universe u as k, so the test
family is not rendered vacuous by a smaller independently chosen universe. The
open U is nonempty because its generic point differs from c; the generic
comparison is therefore not an equality merely on an empty pullback. No
mathematical statement fault or STATEMENT-DISPUTED flag was found.

Searches made:

- `msearch.py ... leanfinder`: “Universal closedness of a quasi compact morphism
  of schemes locally of finite type over a field is equivalent to normal curve
  local lifting tests”. Eight hits, including `UniversallyClosed`, its valuative
  criterion, and finite-global-sections results. None gives the restricted
  normal-finite-type-curve test or the three-condition equivalence.
- `msearch.py ... loogle '"UniversallyClosed"'`: twelve hits, all basic
  definitions and permanence/closed-map facts; no exact match.
- `msearch.py ... grep 'normal.*curve.*closed|curve.*criterion|affine.*space.*closed'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id, the proposed declaration name, and normal-curve closedness
  patterns: no matching statement; unrelated normal-curve results concern
  smoothness, real boundary or valuation modifications. The existing general
  valuative criterion quantifies over all valuation squares and is not a duplicate.

The inherited BLOCKED ending was a stage-1 handoff issue. The current
`coord/brief-stage2.md` §0 explicitly authorizes proceeding in stage 2 after the
reviewed split; `coord/queue.tsv` lists this node at stage 2, and the live node
has no usable Lean record or released repair note. No re-splitting was done.

Validation: the prescribed scompile.py compiled the statement in sandbox and
library modes, cleanly. A first compile reported that IsIntegrallyClosed was
only privately imported; its direct public import repaired that error. The
final delivery dry run checks the finalized direct dependency imports again.

## Second reading by Q28

Worker second pass (not an independent agent; the dispatcher brief forbids
starting agents and assigns independent review to the maintainer): compared the
node and complete Lean signature again. The table above accounts for every
hypothesis and all three conclusions. Rechecked the direction of both pullback
projections in the final equality: snd goes to Spec F, fst to U, so the two
composites have the same source and compare precisely the generic restrictions.
The use of a fibre product is faithful because its projection to Spec F is an
isomorphism by integrality and the dimension-one hypothesis, as explained above.
Rechecked the direction hg in the polynomial product map and included n = 0.
No change to the mathematical statement, new nodes, dependency repairs or
correction audit was necessary.
