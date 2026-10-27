## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralFiniteFibreFpqcAffineDescent` states
`AlgebraicGeometry.exists_representableBy_affine_neighbourhoods_of_integral_fpqc`.
Its only proof is `sorry`. No definitions, auxiliary theorems, new nodes, dependency
repairs, or statement corrections are needed. Only the assigned node's `lean` changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes S, S′, T | `{S S' T : Scheme.{u}}` |
| S locally Noetherian, equivalently an affine cover by Noetherian rings | `[IsLocallyNoetherian S]`; Mathlib's `isLocallyNoetherian_of_affine_cover` and `IsLocallyNoetherian.component_noetherian` give the equivalence |
| Contravariant set-valued functor on S-schemes | `F : (Over S)ᵒᵖ ⥤ Type (u + 1)` |
| fpqc covering equalizer sheaf condition | `hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F` |
| p : S′ → S an fpqc morphism | `p` with `[Flat p] [Surjective p] [QuasiCompact p]`; `Scheme.Hom.singleton_mem_fpqcPrecoverage` identifies its singleton covering |
| F restricted to S′ represented by a locally finitely presented S′-scheme | `P : Over S'`, `[LocallyOfFinitePresentation P.hom]`, and `hP : Nonempty (((Over.map p).op ⋙ F).RepresentableBy P)` |
| Integral, surjective, flat, quasi-compact q : T → S | `q` with `[IsIntegralHom q] [Surjective q] [Flat q] [QuasiCompact q]` |
| Finite underlying fibres of q | `hq : ∀ s : S, (q ⁻¹' {s}).Finite` |
| F restricted to T represented by locally Noetherian Y | `Y : Over T`, `[IsLocallyNoetherian Y.left]`, and `hY : Nonempty (((Over.map q).op ⋙ F).RepresentableBy Y)` |
| Y has (FA), every finite subset lies in an affine open | `hFA : ∀ E : Set Y.left, E.Finite → ∃ U : Y.left.Opens, IsAffineOpen U ∧ E ⊆ (U : Set Y.left)` |
| F represented by an S-scheme X | `∃ X : Over S, Nonempty (F.RepresentableBy X) ∧ ...` |
| X has (FA) | The next conjunct repeats the same finite-subset condition on `X.left` |
| If Y → T is flat, separated and of finite presentation, so is X → S | The final implication, with `Flat`, `IsSeparated`, and `LocallyOfFinitePresentation ∧ QuasiCompact ∧ QuasiSeparated` on the two structure maps |
| Separated means diagonal a closed immersion | Mathlib `IsSeparated`, defined using `IsClosedImmersion (pullback.diagonal f)` |

All variables and the universe `u` are explicitly bound; `autoImplicit` is disabled.
The usual scheme size convention uses schemes in `Scheme.{u}`, Hom sets in `Type (u+1)`,
and functor values in that same universe, matching the landed fpqc representability
interface. `RepresentableBy` supplies natural bijections with every Hom set; `Nonempty`
asks for the representing identification without choosing arbitrary data.
Property (FA) is expanded directly in terms of existing sets, opens and `IsAffineOpen`;
it introduces no alternate named definition. Finite presentation uses the explicit
three-part convention in `def-sbc-locally-finite-presentation`, without a new predicate.

Dependency declarations read and used (the existing records were usable):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; schemes, opens, and affine schemes.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`,
  `Scheme.fpqcTopology`, `Scheme.Hom.singleton_mem_fpqcPrecoverage`.
  `Mathlib.CategoryTheory.Sites.Over` supplies the slice-site restriction.
- `Mathlib.CategoryTheory.Yoneda`: `Functor.RepresentableBy`,
  `Functor.IsRepresentable`, `yoneda`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; the node itself specifies the global finite-presentation
  conjunction. `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (equivalent to stalkwise flatness).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom` (the integral clause
  recorded by `def-weil-finite-integral-morphism`).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; and
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, interpreting the
  affine-cover condition in the node without adding a stronger Noetherian hypothesis.

Non-public proof imports preserve the already stated proof plan:
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`,
`WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent`,
`WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`,
`WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent`,
`WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact`,
`WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover`,
`WeilConjectures.RingTheory.FibreRingNoetherian`,
`WeilConjectures.RingTheory.IntegralExtensionDimension`,
`Sheaf.AlgebraicGeometry.FpqcRepresentabilityDescent`,
`Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent`, and
`Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`.
The other Mathlib proof dependencies are available through the public imports.
The proof-only nodes `lem-sfb-integral-descent-finite-point-orbits`,
`lem-sfb-integral-descent-invariant-quasiaffine-charts`, and
`lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer` have no recorded Lean
module, so there is no module of theirs to import. None is a prerequisite to typing
this statement. The docstring retains all eight accepted proof steps and their node ids.

Edge cases checked before writing: the empty scheme and empty finite set are allowed;
there is no `Nonempty` assumption on any scheme. For E empty, the empty affine open
(Spec of the zero ring) is permitted. The fibre condition is set-theoretic finiteness
on the original q, not universal finiteness or finiteness of q as a scheme morphism.
No finite-type, separatedness, flatness, or global quasi-compactness condition is imposed
on Y beyond the node's hypotheses: the additional three morphism properties occur
only as an antecedent in the final conclusion. No affine or semi-local assumption is
added on S. Arbitrary characteristics and the zero ring remain allowed.

Searches performed:

- `msearch.py ... leanfinder` query: “An fpqc sheaf represented locally by a locally
  finitely presented scheme descends along an integral faithfully flat cover with finite
  fibres and affine neighbourhoods of finite sets”. Eight hits, chiefly property descent
  in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` and `LocallyOfFinitePresentation`;
  none asserts object representability or descent of finite-set affine neighbourhoods.
- `msearch.py ... loogle` query: `"IsIntegralHom", "RepresentableBy"`; zero hits.
- `msearch.py ... grep` query:
  `integral.*[Dd]escent|[Dd]escent.*integral|[Pp]roperty.?FA`, AlgebraicGeometry;
  two hits in FlatDescent about faithful pullback, neither a match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for integral descent, affine
  neighbourhood predicates, property (FA)/(AF), and the exact node id found no matching
  declaration. Related quasi-affine descent and affine neighbourhood theorems do not
  state this object-effectivity result. The exact-id search in WeilConjectures had no hit.

Sources checked: the primary Numdam scan
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf, printed pp.54-55, PDF pages 50-51:
Proposition 4.1.1 gives integral effectivity from affine fibre neighbourhoods; Proposition
4.1.3 (OCR 4.1.5) gives affine-neighbourhood transfer for finite underlying fibres.
These support the node's specialization and (FA) conclusion. The current blueprint
is only an indirect ancestor of this expanded lemma; its own statement is not changed.
No mathematical statement fault was found.

Validation: the initial module passed `scompile.py` in sandbox and library contexts
(15.5 s and 4.4 s); the final header and delivery are checked again by the dry run.

## Second reading by Q84

The dispatcher explicitly forbids starting another agent. This is a separate self-review
pass, not a claim that another worker independently read the delivery; the maintainer's
independent review remains required. With the node and final signature open, I checked
that both restrictions precompose by `(Over.map ...).op`, that the representing object
P lies over S′ while Y lies over T, and that the result quantifies X over S. The
finite-set predicate uses Y.left and X.left, not their bases. The last implication uses
Y.hom and X.hom; the five conjuncts express exactly the three requested properties,
with finite presentation expanded to its three defining conditions. It does not
accidentally require those properties unconditionally. The p and q hypotheses are
separate and the original underlying-fibre condition is retained. No mismatch was found;
the only subsequent edit made all recorded statement-dependency imports explicit.
