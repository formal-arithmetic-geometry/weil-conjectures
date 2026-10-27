## Worker report

Item: lem-sfb-etale-effective-open-chart-descent. Group Q25, stage 2.

The module `Sheaf.AlgebraicGeometry.EtaleEffectiveOpenChartDescent` states
`AlgebraicGeometry.EtaleEffectiveOpenChartDescent.exists_algebraicSpace_of_effective_open_charts`.
Its proof is `sorry`. Three canonical-map helpers, `projection`, `sectionMap` and
`relativeChartMap`, have explicit data and no postponed proofs. They belong to this
criterion, not independent replacement definitions of descent or algebraic spaces.
No DAG statement, dependency list or proof was changed; only the item's `lean` record
is changed. No new nodes or dependency modules are needed.

The source was read at `literature/stacks-project/descent.tex`: definition-descent-datum
(023V), lemma-fpqc-universal-effective-epimorphisms (023Q), and lemma-open-fpqc-covering
(03N0), and `bootstrap.tex`, theorem-final-bootstrap (04S6), especially (3)/(4).
This is an agent local-chart criterion assembled from those results, as the node says;
it is not a general fpqc effectivity assertion. The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was read: paragraph (3) supplies the recorded ancestor route, not a separate statement
of this criterion. No statement correction is necessary.

Hypothesis correspondence:

| Node hypothesis or supplied object | Lean |
| --- | --- |
| Schemes S', S and p : S' -> S | `{S' S : Scheme.{u}} (p : S' ⟶ S)` |
| p flat, quasi-compact, surjective | `[Flat p] [QuasiCompact p] [Surjective p]` |
| Y over S' | `V : Over S'`, with Y = V.left and structure map V.hom |
| Y/S' separated, diagonal closed | `[IsSeparated V.hom]`; Mathlib's class is exactly closedness of the diagonal |
| Descent datum alpha relative to p | `D : Over.DescentDatum p V`; its transport form is the recorded 023V interface |
| Set-indexed open covering | `{I : Type u} (U : I → V.left.Opens) (hcover : iSup U = ⊤)` |
| T_i, r_i, q_i with p = r_i q_i | `T`, `rBase`, `q`, `hp : ∀ i, q i ≫ rBase i = p` |
| Each q_i flat quasi-compact surjective | `hq : ∀ i, Flat (q i) ∧ QuasiCompact (q i) ∧ Surjective (q i)` |
| Each r_i étale | `hr : ∀ i, Etale (rBase i)` |
| T_i-scheme Z_i | `Z : ∀ i, Over (T i)` |
| Supplied Z_i ×_{T_i} S' ≅ U_i | The effective projection `b i : (U i).toScheme ⟶ (Z i).left` and `hpb i : IsPullback (b i) ((U i).ι ≫ V.hom) (Z i).hom (q i)` |
| Stability under restricted alpha | `hchart`: a point `a` factoring through U_i at s₀ transports to a point factoring through U_i at s₁ whenever `s₀ ≫ q i = s₁ ≫ q i` |
| The supplied iso induces the restricted datum | The same `hchart` requires `u₁ ≫ b i = u₀ ≫ b i` |
| Fixed universes, allowed scheme coproducts | All schemes are `Scheme.{u}`, index `I : Type u`, sets `Type u`; the actual coproduct is the Mathlib scheme coproduct of the Z_i.left |

The pullback square `hpb` is equivalent to the supplied isomorphism of S'-schemes:
the unique map from U_i to the selected fibre product is an isomorphism precisely
when the square is Cartesian, and its inverse is the displayed isomorphism in the
node. Thus the projection `b` is supplied data, not an arbitrary auxiliary map.
The transport condition is universally tested on schemes, not just topological
points. Since an open immersion is mono, `u₁` is unique whenever it exists.
Testing the reversed pair gives stability in the reverse direction. Together with
`hpb`, invariance under `b` says exactly that the transported point is the canonical
transport on the pullback of Z_i. This combines the two chart compatibility hypotheses
without strengthening or dropping either one. There is no extra datum of a global
scheme model of Y over S.

Conclusion correspondence:

| Node conclusion | Lean |
| --- | --- |
| X is an algebraic space on the big fppf site | `∃ X : AlgebraicSpace S`; this is the recorded full subcategory of fppf sheaves having a representable diagonal and a surjective étale scheme atlas |
| X ×_S S' ≅ Y | `r : ((Over.map p).op ⋙ X.obj.obj).RepresentableBy V`, a natural representing isomorphism on the S'-site |
| This iso induces alpha | The first conjunct equates `r.overDescentDatum.transport` and `D.transport` on every point and pair of lifts |
| X(T) is exactly the displayed equalizer | The second conjunct says `sectionMap ... W` is injective, and `y` lies in its image iff it satisfies the alpha-matching equation |
| Restriction in X is pullback | `X.obj.obj` is a presheaf functor; `sectionMap` restricts along the canonical projection then applies the natural representation `r.homEquiv.symm` |
| Each supplied Z_i maps to X | `c i : yoneda.obj (Over.mk ((Z i).hom ≫ rBase i)) ⟶ X.obj.obj` |
| Each Z_i -> X is representable étale | `∀ i, AlgebraicSpace.IsEtale (c i)`; this recorded predicate includes scheme representability |
| Collectively the maps give a surjective étale scheme atlas from the coproduct | `atlas` has domain the Yoneda presheaf of `Over.mk (Sigma.desc ...)`; it is `IsEtale` and `IsSurjective`, with `yoneda.map (Sigma.ι ...) ≫ atlas = c i` |
| Over T_i, Z_i -> X ×_S T_i is representable open | `IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) (relativeChartMap ... (c i))` |
| Its pullback by q_i is the supplied U_i -> Y | The final `IsPullback` square has left edge the Yoneda image of U_i -> Y, top edge the supplied b_i, right edge the relative chart map, bottom edge the pair of `projection ... r` and Y -> S' -> T_i |

To read the equalizer clause, fix W -> S. The point `y` is an S'-map
`W ×_S S' -> Y`. For every A, `t : A -> W`, and two lifts `s₀,s₁ : A -> S'`
over that t, the maps `pullback.lift t s₀ h₀` and `pullback.lift t s₁ h₁`
are its two restrictions. The stated equation transports the first by D and
identifies it with the second. This is precisely alpha(p₀* y) = p₁* y:
the universal double product is one of these tests, and conversely each such
pair factors through that double product. The injectivity and image condition
give the actual canonical natural bijection with the equalizer, rather than
an unrelated algebraic space or arbitrary identification of underlying sets.
The representation `r` and functorial restriction give its naturality.

`projection` is the Yoneda map of `r.homEquiv (𝟙 V)`, hence canonical for this
base-change identification. `sectionMap` is its adjoint restriction on tests.
`relativeChartMap` is literally `prod.lift` of the chart and its structure map.
The products in presheaves on Over S are products over the base S, whose
represented sheaf is terminal. Thus the last square really is base change by
q_i, using X ×_S S' ≅ Y; its top edge forces the chart map to be the one supplied
by the effective chart. These helpers introduce no additional hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated` and `.ClosedImmersion`:
  `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum`, its transport and cocycle fields,
  `Functor.RepresentableBy.overDescentDatum`; the full signatures and docstrings
  were read, including `IsEffective`, which is not used because X need not be a scheme.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  each U_i is an actual open subscheme with its canonical inclusion.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and
  `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Limits.pullback`, its projections,
  lift and `Over.pullback`; the latter uses the second projection as structure map.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, used as
  `Scheme.fppfTopology.over S` by the recorded algebraic-space definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `IsRepresentableWith` and `IsAlgebraicSpace`, read in full.
- The scheme-conventions and size-convention nodes explicitly define no new
  Lean object; the existing properties and explicit universes implement them.

Proof dependency modules are imported, including
`WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent` for
`openSubscheme_existsUnique_of_fpqc`, the Mathlib precoverage, open immersion,
étale, coproduct, locality and finite-limit modules, and
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` for `schemeSpace`.
`lem-sfb-fppf-space-atlas-bootstrap` currently has no recorded declaration or
Mathlib match, so there is no module to import for it. It is used only in the
natural-language proof, not to define any object or hypothesis in this statement.
It was not restated as an additional postponed theorem.

Edge cases checked before writing and again against the final signature:

- I empty: `iSup U = ⊤` forces Y empty; no `Nonempty I` appears. The coproduct
  and descended space may be empty, including when S is nonempty.
- Individual U_i empty: hpb then makes its pulled-back Z_i empty. Since q_i is
  surjective, Z_i is empty. Empty summands and their étale maps are allowed.
- p = identity: matching sections identify with actual Y-points, and the criterion
  recovers Y with the specified charts. No special-case hypothesis excludes this.
- T_i = S: the relative chart map is open; general T_i is only étale over S,
  so the theorem requires c_i to be étale, not globally open.
- S empty or S' empty: the surjectivity condition is retained. All scheme and
  section types remain meaningful, including an empty atlas.
- Arbitrarily many charts within the fixed size bound: no finite index, affine,
  quasi-compact chart, noetherian base, or finite-presentation condition on Y was added.
- Nontrivial alpha: the equality with its transport is retained explicitly;
  neither identity transport nor general scheme effectivity was assumed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "An fpqc scheme descent datum with effective open charts over etale base neighbourhoods defines an algebraic space with these charts as an etale atlas"`:
  8 results, only Scheme.Etale, étale sites/pretopologies/forgetful functors,
  and IsEtale. None is this effectivity criterion.
- `msearch.py ... loogle '"DescentDatum", "IsOpenImmersion"'`: 0 results.
- `msearch.py ... grep 'DescentDatum|descent.*[Ee]qualizer|[Ee]ffective.*[Oo]pen' AlgebraicGeometry`:
  1 result, EffectiveEpi.lean:125, exists_openCover_exists for effective epis;
  no algebraic-space effectivity criterion.
- `msearch.py ... leansearch "An fpqc descent datum for a scheme with effective open charts over etale neighbourhoods defines an algebraic space"`:
  8 results on scheme and locally ringed-space gluing and local representability.
  These glue open charts over a Zariski sheaf and do not state the present criterion.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for DescentDatum,
  descendedPresheaf, descentPresheaf, equalizer/descent, and effective open charts:
  found the recorded transport interface, descent of representing objects,
  group-valued descendedPresheaf, scheme descent, and algebraic-space fpqc sheaf
  results; none gives the present matching functor with the supplied effective charts.
  `rg` for the exact node id in WeilConjectures returned no occurrence.
  The would-be declaration and namespace were also absent from the upstream name
  index and the source trees. No existing statement was duplicated.

Validation: `scompile.py Q25 lem-sfb-etale-effective-open-chart-descent <module>`
compiled both sandbox and named library module cleanly (2.1 seconds each) before
adding explicit dependency imports. The final import-complete file also passed the mandatory delivery dry run:
`OK (dry run): commit 7906365f1b0 passes the preflight and compiles; nothing pushed`. All variables and the universe are
explicitly bound, with `set_option autoImplicit false`. All lines are at most
100 characters. The only postponed proof is the main theorem, whose docstring
contains all ten proof steps with their DAG inputs. No statement dispute was found.

## Second reading by Q25

Worker self-check, not a claim of an independent second worker: the dispatcher
brief prohibits starting other agents and assigns independent review to the
maintainer. With the node and completed file open, I rechecked all rows above.
In particular hchart includes stability as well as effective-datum compatibility;
the Cartesian conclusion retains b_i and U_i -> Y; the equalizer identification
is natural through restriction and the representing object; and the atlas is
from the actual scheme coproduct with all summand restrictions recorded.
Compiler repairs supplied explicit Over source/target objects and normalized
commutative-square equations; these did not change the mathematical statement.
No additional mismatch or node correction was found.
