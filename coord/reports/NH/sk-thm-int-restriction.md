## Worker report

The module `Sheaf.SixFunctors.IntegralExceptionalRestriction` states
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.integralExceptionalRestriction`.
Its only theorem proof is `sorry`. The helper `ctfRestrictionAssertions` is a fully written
Prop-valued encoding of the two conclusion clauses, not another coefficient, constructibility,
localizing-closure, or functor definition. The node changes only in `lean`.

Source read: blueprint main-20261015,
`sec-six-functors-basics/sk-thm-int-restriction/_section.md` and
`sk-thm-int-restriction.proof.md`, against the item's five expanded DAG proof steps.
The theorem docstring records those five steps, including their cited nodes and the explicit
noncircular use of only clause (1) of the gluing theorem.

Hypothesis and clause correspondence:

- The standing prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The finite extension inside the fixed algebraic closure is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`; its condensed valuation ring is exactly
  `Profinite.padicIntegersRingObj ℓ E.val`. Its pulled-back internal-module coefficients
  are those used by `Ambient`, `constantModelBoundedConstructible`, and the recorded
  `ConstantModelConstructibleFiniteTor`. No discrete constant valuation-ring sheaf is used.
- The standing field has `(k : Type u) [Field k] [Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ ℓ)]`, encoding positive characteristic different from ℓ.
- X and Y are arbitrary `Scheme.{u}` with their `Over (Spec (.of k))` instances.
  For each structure map, `LocallyOfFiniteType` and `QuasiCompact` mean finite type,
  and `IsSeparated` is the standing separatedness assumption. There is no smoothness,
  regularity, properness, nonemptiness, or algebraic-closedness assumption.
- The morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` with
  `[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`, exactly a separated
  finite-type k-morphism.
- `c : Compactification.BoundaryCompactification f` is the recorded compactification
  datum. Its underlying compactification `c.obj.obj` is fed to the actual image functor.
  The statement works for any such fixed datum, in particular the chosen one; the
  construction node supplies compactification independence.
- `h` is the preservation evidence needed to type the recorded `lowerShriek` restriction
  on Loc(Dbc). `G` and `_adj : lowerShriek ... h ⊣ G` name the Brown right adjoint and
  its adjunction. They are supplied by `exists_integralBrownAdjoint`; these binders
  specify the right adjoint already named in the node, rather than assuming its
  constructibility. The dependency intentionally makes no nonunique choice of G.
- Dctf is the recorded full subcategory
  `ConstantModelConstructibleFiniteTor Λ T`, definitionally on
  `constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _`.
  The helper's existential `hY` is the inclusion Dctf(Y) ≤ Loc(Dbc(Y)), a conclusion
  justified directly by the defining localizing intersection. It is not a premise.
- Preservation of Dctf by f^! is exactly `hR`: for every object K of Dctf(Y),
  the ambient object of `G.obj ((ObjectProperty.ιOfLE hY).obj K)` satisfies the
  conjunction of bounded constant-model constructibility and finite Tor amplitude.
  Membership proofs do not change objects or morphisms. Therefore this covers
  any representative of K in the localizing full subcategory by proof irrelevance.
- `hL` records that the already defined compact-support composite sends Dctf(X)
  to Dctf(Y), as required to type the left restricted functor mentioned in the node.
- The second sentence is `Nonempty (L ⊣ R)` with L and R written explicitly as
  `ObjectProperty.lift` of those actual ambient composites. L is the inclusion of
  Dctf(X) followed by `image Λ c`; R is `ιOfLE hY ⋙ G ⋙ (localizing Λ X).ι`.
  They retain exactly the original objects, maps, and ambient Hom sets. `Adjunction`
  includes naturality in both variables. No arbitrary replacement functors are used.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, its full signature,
  and the module's setting and compactification docstrings. This setting is rendered by
  the explicit field, structure-map and k-morphism binders; a separate setting predicate
  would duplicate it. The actual compactification is the datum used by the Brown node.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`, and
  `ConstantModelConstructibleFiniteTor`; full definitions and docstrings read.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `IsLocalizingAdmissibleCoefficient` and its imported original
  `CategoryTheory.localizingClosure` / `localizingClosureProEtale` from
  `Sheaf.Paper.LocalizingClosure`. Definitions and coefficient cases read.
  The precise integral specialization is already `IntegralCompactSupport.localizing`
  from the compact-support construction, which uses these original closure definitions.
- `det-prop-int-brown-adjoint`: `Sheaf.SixFunctors.IntegralBrownAdjoint`,
  `IntegralCompactSupport.lowerShriek`, `brownAdjointAssertions`, and
  `exists_integralBrownAdjoint`; complete module read. The item uses its exact G domain,
  codomain, left functor, membership evidence, compactification and coefficient object.

The available proof-dependency modules are imported non-publicly, with the four statement
modules public. In particular the module imports `IntegralLocalizingCompactSupport`,
`LocalizingClosureCtfEqualsBc`, `IntegralTensorInverseImage`, and the Mathlib finite-type,
closed-immersion, affine, quasi-compactness and quasi-separatedness modules.
The proof nodes `det-sf-mate-open-restriction`, `det-thm-int-restriction-line`,
`det-thm-int-restriction-closed`, and `det-thm-int-restriction-glue` have no recorded
Lean declarations at inspection; they are proof prerequisites only, so no nonexistent
module is imported. Their roles are fully recorded in the theorem proof docstring.

Edge cases checked before writing: empty X or Y, zero complexes, identity morphisms,
open and closed immersions, zero-dimensional affine charts, and E = Q_ell are not excluded.
There is no chosen cohomological or Tor interval: each object's finite interval may vary.
The site has the established scheme universe u, internal abelian coefficients u+1, and
ordinary unbounded module-object derived categories. No new universe identification or
size restriction is imposed. The assertion does not assume the output is constructible.

Searches performed for an existing statement:

- msearch leansearch: `Exceptional inverse image preserves integral constructible complexes`.
  Eight results about constructible subsets, preimages and scheme restrictions; none is
  a statement about exceptional pullback on integral module-object derived categories.
- msearch leanfinder: `The exceptional inverse image right adjoint to compact support
  pushforward preserves constructible integral l-adic complexes`.
  Eight results about ordinary module/sheaf pushforward adjunctions and locally constant
  condensed modules; no match for the integral Brown restriction theorem.
- msearch loogle: `CategoryTheory.Adjunction, CategoryTheory.ObjectProperty`.
  Three results: `IsCoseparating.strictMap_rightAdjoint`,
  `IsSeparating.strictMap_leftAdjoint`, and `Adjunction.isCardinalFilteredGenerator`.
  These do not assert geometric constructibility preservation.
- msearch grep: `integral.*[Rr]estriction|[Bb]rown[Aa]djoint|exceptional.*constructible`.
  Four unrelated integral-closure/measure-theoretic integral hits; no match.
- rg of the upstream `WeilConjectures` source for the item id has no hits.
  Keyword searches of upstream and `lean/Sheaf` locate the recorded integral Brown
  modules and generic restriction/adjunction material, not the item's theorem.
  The upstream pro-etale `Derived.UpperShriek` instance is for a right adjoint constructed
  directly on the upstream bounded-constructible category; it does not state that
  this Brown adjoint on the recorded constant-model localizing category preserves Dctf.
  The side framework's exact `Derived.BoundedConstructible` and `Derived.UpperShriek`
  sources were opened; no second definition or existing-match attachment is appropriate.

No new nodes, dependency repairs, statement correction, or mathematical dispute.

## Second reading by NH

The dispatcher forbids starting other agents; this section records the author's second
reading, with independent mathematical review left to the maintainer as specified in the
brief. I reopened the node and checked both sentences against the helper and theorem.
The positive-characteristic, ℓ-invertibility, scheme finite-type/separated and k-morphism
hypotheses appear explicitly. The coefficient is the condensed O_E, not an ordinary ring
sheaf; Dctf is the exact recorded constant-model finite-Tor category, not upstream Dbc.
I checked that G is the right adjoint of precisely `IntegralCompactSupport.lowerShriek`
and that hR concludes finite Tor amplitude as well as bounded constructibility. I checked
that the restricted left functor is the actual compactification image and the right one
is the actual G, rather than merely asserting existence of some adjoint on Dctf. hY, hL,
and hR are existential conclusions; in particular no output-preservation hypothesis is
smuggled into the binders. The five-step proof docstring uses finite-cover locality only,
avoiding the circular second clause of the glue node. Added the explicit quasi-compactness
proof import during this reading. No change to the node's mathematical statement was needed.

Validation: `scompile.py NH sk-thm-int-restriction` compiled the sandbox and module cleanly
with no errors or warnings. `deliver2.py NH sk-thm-int-restriction --no-push` printed
`OK (dry run): commit a09f090602 passes the preflight and compiles; nothing pushed`.
The JSON signature is verbatim from the file; comparison against the base found only
`lean` changed. The file contains one theorem and its single expected `sorry`.
