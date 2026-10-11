## Worker report

The main module is `Sheaf.Topology.ClosedPushforwardBoundaryNaturality`, declaring
`TopCat.Sheaf.closed_pushforward_boundary_naturality`. The item's TeX statement is unchanged.
The theorem has a `sorry` proof, and its docstring contains the three node-proof steps, with
step 2 expanded into the two universal-property arguments. A dependency module supplies the
previously unrecorded canonical connecting-map structure on the existing cohomology groups.
A new DAG node supplies the packaged delta-functor structure; the item TeX statement is unchanged.

Hypotheses and clauses of the item, in their order:

1. Schemes Z and X and their closed immersion are `{Z X : Scheme.{u}} (i : Z ⟶ X)
   [IsClosedImmersion i]`. The underlying continuous map is `Scheme.forgetToTop.map i`.
   There are no properness, Noetherian, nonemptiness, characteristic or field hypotheses.
2. Abelian sheaves on the small Zariski site are `(Z : TopCat).Sheaf AddCommGrpCat.{u}`.
   `ShortComplex` retains both arrows, and `S.ShortExact` says exactly that
   `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact. S is quantified in all the relevant clauses,
   so the construction works simultaneously for all sequences, as a delta-functor must.
3. Direct image is Mathlib's `pushforward AddCommGrpCat (Scheme.forgetToTop.map i)`.
   Its object on an open U is the original sheaf on `i⁻¹(U)`; for a closed embedding this
   is U intersected with Z under the identification with the closed image. It is not the
   direct image of modules over the structure sheaves.
4. Exactness of direct image is the existential witness `hex`, providing the short-exact
   proof for every `S.map pushforward`. No exactness hypothesis has been added.
5. `T : CohomologicalDeltaFunctor ... AddCommGrpCat.{u + 1}` packages the asserted target
   delta-functor. `e n` is a natural isomorphism from `T.F n` to
   `pushforward ⋙ abelianCohomologyFunctor X n`. Its boundary-compatibility clause fixes
   the connecting maps to the canonical boundaries of the image sequences. This clause
   is essential: neither T nor its connecting maps are arbitrary. The auxiliary
   natural isomorphisms allow representation by any isomorphic model of the target.
6. The source is `abelianCohomologyDeltaFunctor Z`, whose F and delta fields are explicitly
   the existing global H' functors and canonical Ext boundaries. `t` is a
   `CohomologicalDeltaFunctor.Hom` from that source to T, so naturality in every sheaf
   morphism and compatibility in every degree with every sequence are part of its type.
7. The degree-zero identity is the first condition on t: after applying `e 0`, the
   target degree-zero class has exactly the same global section as the source class.
   `abelianCohomologySection` is evaluation of `Ext.addEquiv₀` on the free generator
   at the whole space, after the sheafification unit. It is the canonical H⁰=Γ
   identification, not a freely chosen equivalence. The global sections of direct
   image at X are definitionally the sections on Z.
8. Uniqueness is explicitly over every `t'` of the same delta-functor-Hom type with that
   degree-zero identity, and asserts `t' = t`. It is uniqueness from degree zero alone,
   not uniqueness only among isomorphisms or among morphisms satisfying the extra clauses.
9. Every degree is an isomorphism: `∀ n : ℕ, IsIso (t.app n)`. Together with `e n` this
   gives the natural cohomology comparison in the node, including its degree-zero case.
10. For every short exact S and `c : H⁰(Z,S.X₃)`, the next conjunct explicitly states
    `e₁(t₁(δ_Z(c))) = δ_X(e₀(t₀(c)))`. The degree-zero identity identifies the expression
    on the right with δ_X(i_*c). Both boundaries are the fixed Ext-class boundaries.
11. The constant-integer specialization uses isomorphisms `a` and `b` from the original
    and pulled-back quotients to Mathlib's constant sheaf on `AddCommGrpCat.of (ULift ℤ)`.
    This includes the literal constant quotients by taking identity isomorphisms, and
    allows the conventional identification of the quotient rather than requiring a
    syntactically identical sheaf.
12. The pulled-back image sequence is `P`, `hP`, and a morphism `φ : P ⟶ S.map pushforward`.
    `IsPullback φ.τ₂ P.g (S.map pushforward).g φ.τ₃` is exactly its pullback square.
    The canonical kernel identification is the map `φ.τ₁`; the final boundary equation
    transports the class along `(abelianCohomologyFunctor X 1).map φ.τ₁`.
13. `hcZ` and `hcX` identify cZ and cX with the global section one via the constant-sheaf
    adjunction units applied to `ULift.up 1`. `hu` says the quotient map sends this one
    to the original one. The final equation is the typed equality after mapping the
    pullback boundary along `φ.τ₁`, with no HEq hypothesis or conclusion.

Dependency declarations opened and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Sites.Spaces`: `Opens.grothendieckTopology`; and
  `Mathlib.Topology.Sheaves.Sheaf`: `TopCat.Sheaf`, giving the small Zariski site encoding.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H'` and its
  underlying `cohomologyPresheafFunctor`. The dependency module evaluates precisely this
  functor at `op ⊤`; hence its groups are definitionally the recorded H', with the same
  `HasExt.standard` as the comparison dependency.
- `Sheaf.CategoryTheory.DeltaFunctor`: `CategoryTheory.CohomologicalDeltaFunctor` and its
  `Hom`. All fields, including exactness and naturality, were read.
- `Sheaf.Topology.ClosedImmersionPushforwardExact`:
  `TopCat.Sheaf.shortExact_map_pushforward_closedSubset`, read as the exactness proof input.
  Its subtype presentation is not an extra hypothesis in this statement.
- `Sheaf.Topology.ClosedImmersionPushforwardCohomology`:
  `TopCat.cohomology_closed_immersion_pushforward`, read as the injective effacement proof
  input. Its `Nonempty` isomorphism alone does not specify boundaries, so the present
  statement does not pick that arbitrary isomorphism as t.
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`:
  `CategoryTheory.Functor.exists_universal_rightDerived_deltaFunctor`, read as the source
  universality proof input.
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`:
  `CategoryTheory.effaceable_deltaFunctor_isUniversal`, read as the target universality
  proof input. These last four theorem modules are not unused imports: they are named in
  the natural-language proof, while the theorem signature uses the shared definitions.

Additional Mathlib data used: `ShortComplex.ShortExact.extClass`, `Abelian.Ext.postcomp`,
`Abelian.Ext.addEquiv₀`, `sheafificationAdjunction`, `yoneda`, `AddCommGrpCat.free`,
`constantSheaf`, `constantSheafAdj`, and `IsPullback`. These keep the boundaries and global
sections tied to actual cohomology classes, rather than arbitrary maps.

Edge cases checked before writing: the identity closed immersion gives the identity
comparison; the empty Z has only zero abelian sheaves and zero cohomology, including
H⁰ of the constant sheaf and its distinguished section; X empty forces Z empty; zero
sheaves and split exact sequences have zero boundaries; n=0 is explicitly included,
with no positive-degree-only restriction. The group and space universes may be enlarged
jointly, so this encoding covers arbitrarily large abelian sheaves and schemes. H' uses
`HasExt.standard` in universe u+1, exactly as the existing comparison module; this is a
choice of Ext representative, not an additional hypothesis. No disputed statement found.

Searches (also logged in the sandbox searches.jsonl):

- msearch/leanfinder: “closed immersion pushforward sheaf cohomology comparison commutes
  with connecting boundary maps”: eight hits, mainly module pushforward-composition
  isomorphisms and module pullback; none state the item or package its canonical boundaries.
- msearch/loogle: `CategoryTheory.Sheaf.H', CategoryTheory.ShortComplex.ShortExact.extClass`:
  zero hits. Direct source reading located H' and extClass in the pinned Mathlib.
- msearch/grep: `pushforward.*boundary|connecting.*pushforward` in CategoryTheory:
  zero hits.
- msearch/leansearch: “sheaf cohomology connecting morphism global sections Ext”:
  unavailable (Internal Server Error); no mathematical verdict inferred from unavailability.
- rg in upstream WeilConjectures and landed Sheaf for
  `pushforward.*boundary|connecting.*pushforward|lem-sc-closed-pushforward-boundary-naturality`:
  no match. The exact blueprint-id lookup is included in this search.
- rg for `HFunctor|deltaFunctor|cohomologyFunctor|constantSheaf|connectingHom` in landed
  topology/category modules, upstream topology, and Mathlib sheaf cohomology: H', H,
  cohomologyPresheafFunctor, functorH, Ext boundaries and unrelated Čech constructions;
  no canonical topological cohomology delta-functor record or statement of this item.
- rg in Mathlib, upstream, landed Sheaf and dag/lean_names_upstream.json for all five
  `abelianCohomology...` declaration names and `closed_pushforward_boundary_naturality`:
  no name clashes.

Source read online because this clone contains the literature indices but not the Stacks
source tree: https://stacks.math.columbia.edu/tag/02UV (closed direct-image cohomology),
https://stacks.math.columbia.edu/tag/01DZ (universal global-cohomology delta-functor), and
https://stacks.math.columbia.edu/tag/010Q (delta-functor laws).

Local validation: lcompile.py with the dependency module followed by the item module
compiled both together, exit 0, with no errors or warnings. The only postponed proofs
are `abelianCohomologyDeltaFunctor_laws` and `closed_pushforward_boundary_naturality`.

## New nodes

`def-sc-topological-abelian-cohomology-delta-functor`: the record `CategoryTheory.Sheaf.H'` supplies
cohomology groups but not a chosen canonical long-exact-sequence boundary or packaged
`CohomologicalDeltaFunctor`, both required by this item's actual statement. The new
`Sheaf.Topology.AbelianCohomologyDeltaFunctor` uses those same H' groups at the whole space
and supplies their existing-definition-compatible delta-functor structure. The functor
is just `cohomologyPresheafFunctor ⋙ evaluation(op ⊤)`; its connecting map is postcomposition
with `ShortExact.extClass`. Its section identification evaluates the degree-zero Ext
morphism on the sheafified Yoneda generator. All data are written in full. Only the
proofs of the delta-functor laws are postponed in the named theorem
`abelianCohomologyDeltaFunctor_laws`, with the complete natural-language proof in its
docstring; the definition's proof fields refer to that theorem. The module does not
replace the H' carrier, introduce another cohomology theory, or choose unknown data from
an unproved existence claim. Enough injectives and abelianness are the existing Mathlib
instances for topological abelian sheaves. The scheme specialization is their underlying
space's small Zariski site. This is a new definition node, because no existing declaration packages the required
delta-functor structure; its module records the missing canonical boundaries and section map.

## Earlier Lean rendering repair (not a node statement correction)

The item TeX was unchanged. An earlier
Lean rendering was repaired because its final HEq compared terms whose cohomology
objects have different types, while h₁ only compared the corresponding Hom types. The
source Lemma 02UV identifies the kernel through the canonical map φ.τ₁; accordingly h₁
was removed and the boundary is transported by
`(abelianCohomologyFunctor X 1).map φ.τ₁`. Citer `lem-sc-torsor-h1-functoriality`
holds: it uses this comparison and its boundary naturality abstractly.

## Second reading by U1

Step 1 list and verdicts: (1) `Z X : Scheme.{u}`, closed immersion `i` is rendered by
`{Z X}` and `[IsClosedImmersion i]`; no field, Noetherian, characteristic, or nonempty
hypothesis is added. (2) A short exact sequence `S` of abelian sheaves on the small
Zariski site is rendered as `ShortComplex ((Z : TopCat).Sheaf AddCommGrpCat.{u})` with
`S.ShortExact`. (3) Direct image is exactly Mathlib's `pushforward AddCommGrpCat`
along `Scheme.forgetToTop.map i`. (4) Exactness is the existential `hex`, quantified for
all `S` and proofs `hS`. (5) The target delta-functor `T`, comparison isomorphisms `e`,
and their boundary compatibility are all explicit. (6) `t` is a
`CohomologicalDeltaFunctor.Hom` from `abelianCohomologyDeltaFunctor Z` to `T`. (7) Its
zero-degree identity is expressed by `abelianCohomologySection`. (8) Uniqueness quantifies
over every competing `t'` satisfying the same identity. (9) `∀ n, IsIso (t.app n)` gives
the comparison in every degree. (10) Boundary naturality is stated for every `S`, `hS`,
and degree-zero class `c`. (11) The constant-integer specialization uses isomorphisms to
`constantSheaf` of `ULift ℤ`. (12) The pullback data `P`, `φ`, and `IsPullback` are explicit,
with the kernel map `φ.τ₁`. (13) `hcZ`, `hcX`, and `hu` identify the distinguished section
and the final equality transports the boundary along `(abelianCohomologyFunctor X 1).map
φ.τ₁`. All clauses and quantifier order match the node.

Edge cases checked: identity and empty closed immersions, empty schemes, zero sheaves,
split exact sequences, and degree `n = 0`; all are admitted by the unrestricted binders.
Universes are shared as `Scheme.{u}`, sheaves in `AddCommGrpCat.{u}`, and cohomology in
`AddCommGrpCat.{u+1}`. No characteristic or finiteness restriction is present.

Searches found no existing declaration in Mathlib, `WeilConjectures`, or landed `Sheaf`
for the item or its canonical boundary comparison. The new dependency node
`def-sc-topological-abelian-cohomology-delta-functor` is necessary and records the
canonical Ext boundary and degree-zero section identification; its module has no hollow
definition and only the named delta-functor-law theorem remains sorry. The item module and
dependency module were compiled together successfully with `lcompile.py`; only those two
named proofs are postponed.

No statement mismatch was found. The worker's prior typed repair (transporting the
pullback boundary along `φ.τ₁` and removing the ill-typed HEq premise) is retained. The
sandbox node copy includes the new dependency in `stmt_deps`; the node's `lean.statement`
is verbatim the theorem signature.
