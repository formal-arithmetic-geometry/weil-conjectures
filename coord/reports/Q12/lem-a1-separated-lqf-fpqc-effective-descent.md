## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent` states
`CategoryTheory.Over.DescentDatum.isEffective_of_isSeparated_isLocallyQuasiFinite_fpqc`.
Its only theorem has proof `sorry`; there are no new definitions. The node is unchanged
except for `lean`. No statement correction or disputed statement is needed.

Clause-by-clause correspondence:

- The two schemes and morphism are `{T' T : Scheme.{u}} (f : T' ⟶ T)`.
  The universe `u` is explicitly declared and arbitrary.
- The singleton fpqc covering is
  `hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage T`.
  This is the recorded definition, not a substitute requiring `QuasiCompact f`.
  `fpqcPrecoverage` is the flat quasi-compact covering precoverage; its finite covering
  condition with quasi-compact opens is equivalent to the affine-open version in the node,
  by refining quasi-compact opens into finitely many affine opens.
- A scheme over T' is `{V : Over T'}`; its structural map is `V.hom`.
- Separatedness is `[IsSeparated V.hom]`, whose definition is that the diagonal is a
  closed immersion. Properness is not assumed.
- Local quasi-finiteness is `hV : V.hom.IsLocallyQuasiFinite`, exactly the recorded
  Stacks predicate, including local finite type. Mathlib's weaker stalk predicate is
  not substituted.
- The isomorphism on the double fibre product and cocycle on the triple fibre product
  are represented by `D : Over.DescentDatum f V`. The recorded upstream declaration
  uses natural transport of points, with identity and composition laws. As explained
  in its docstring, Yoneda identifies it with precisely the isomorphism and cocycle of
  Stacks 023V: evaluate transport on the universal pair of projections; its composition
  law is the triple-product cocycle. The identity and invertibility follow from that
  cocycle, so this encoding adds no geometric hypothesis.
- The full conclusion is `D.IsEffective`. Its definition is an existential `V₀ : Over T`
  and `q : V.left ⟶ V₀.left` with `IsPullback q V.hom V₀.hom f`, together with invariance
  under the given transport. The Cartesian square yields the requested isomorphism
  `V₀.left ×_T T' ≅ V.left` over T'. Transport invariance says this isomorphism identifies
  the canonical datum with D; this clause is not omitted.
- There are no assumptions of quasi-compactness, finite presentation or separatedness
  on either base, and no quasi-compactness assumption on `V.hom`. Neither a Noetherian
  nor an affine hypothesis is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`,
  defined in its imported `Morphisms.Separated` as a closed diagonal.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and `IsQuasiFiniteAtPoint`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and `CategoryTheory.Over.DescentDatum.IsEffective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` (the fibre products
  underlying the interpretation of the descent datum and Cartesian square).

Proof-only imports retain the available plan: `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`
(`Scheme.Hom.isLocallyQuasiFinite_resLE`),
`Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`
(`Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`),
`Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.compactSpace_of_isAffine`),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
(`quasiSeparatedSpace_of_isAffine`, `quasiCompact_of_compactSpace`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`
(`IsQuasiAffineHom`, `IsQuasiAffineHom.of_locallyQuasiFinite`).
The proof dependency `lem-a1-ind-quasi-affine-fpqc-effective-descent` currently has no
recorded module, so no import for it can be added yet. It is needed only by the future
proof, not to type this statement. The docstring includes its use and the whole two-step
node proof, expanded to show every input of Zariski's Main Theorem.

Source grounding: read `literature/stacks-project/more-groupoids.tex`,
`lemma-ind-quasi-affine` (Tag 0APK, line 3091 onward), and
`literature/stacks-project/more-morphisms.tex`,
`lemma-etale-separated-ind-quasi-affine` (Tag 0AP9, line 19681 onward).
The former permits any fpqc covering with ind-quasi-affine objects; the latter explicitly
states that every separated locally quasi-finite morphism is ind-quasi-affine. Neither
source adds quasi-compactness or finite presentation here.

Edge cases checked: the empty V is permitted and descends to the empty T-scheme.
For empty T, any scheme mapping to it is empty, and the statement still includes this
case. For the identity covering, any given cocycle descent datum is canonically trivial
and effective. An infinite disjoint union of copies of T' is separated and locally
quasi-finite but need not be quasi-compact; it is admitted. A general separated locally
quasi-finite map need not be quasi-affine as a whole, so the existing quasi-affine descent
theorem would not state this node. Non-separated bases and non-quasi-compact V are
retained by the absence of corresponding hypotheses. No independent smaller test-scheme
universe is introduced: transport quantifies over the same category of schemes.

Searches, all performed 2026-10-18:

- `msearch.py ... leanfinder`: “Descent data for separated locally quasi finite schemes
  along a singleton fpqc covering are effective as schemes without quasi compactness”.
  Eight hits, concerning affine transition limits, generic pseudofunctor stack descent,
  and precoherent pullbacks. None constructs this descended scheme under these hypotheses.
- `msearch.py ... loogle`: `"DescentDatum", "IsEffective"`. Zero hits.
- `msearch.py ... leansearch`: “A descent datum on a separated locally quasi finite scheme
  over an fpqc covering is effective without quasi compactness”. Eight hits: generic
  stack descent, descent of morphism properties, and quasi-separated diagonal facts;
  none is the effective descent statement.
- `msearch.py ... grep`:
  `ind.?quasi.?affine|separated.*quasi.?finite.*descen|descen.*quasi.?finite`. Zero Mathlib hits.
- `rg` on upstream `WeilConjectures/` and project `lean/Sheaf/`, for effectiveness,
  descent/quasi-finiteness, the item's id, and the proposed declaration name.
  Upstream `isEffective_of_isFinite` requires a finite locally free cover and affine
  neighbourhoods of finite sets, so is not this statement. The project's
  `isEffective_of_isQuasiAffineHom_fpqc` requires a quasi-affine structural morphism,
  so does not cover this non-quasi-compact generality. No exact match or name collision.
- `rg` on `dag/lean_names_upstream.json` for the proposed name and separated-lqf descent:
  no match. No duplicate notion or helper is introduced.

Validation: prescribed `scompile.py Q12 lem-a1-separated-lqf-fpqc-effective-descent
lean/Sheaf/AlgebraicGeometry/SeparatedLqfFpqcDescent.lean` passed both sandbox and library
compilation, each in 2.2 seconds, with no warnings or errors.

## Second reading by Q12

Author's separate self-check, with the node and completed module open; independent review
is left to the maintainer as required by this dispatch. The two bases, morphism, fpqc
singleton, separatedness and Stacks local quasi-finiteness all have exactly the binders
listed above. I re-read the upstream `DescentDatum` and `IsEffective` definitions: the
former carries the cocycle, and the latter includes transport compatibility in addition
to the Cartesian square. Thus the conclusion is not merely representability after base
change. All exclusions explicitly disallowed by the node are absent. The only universe
is arbitrary `u`. Every variable is explicitly bound, every declaration has its source
and blueprint id, the theorem's proof is only `sorry`, and the module includes the
available proof-dependency imports. No mismatch or correction was found on this reading.
