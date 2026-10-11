## Worker report

The module `lean/Sheaf/AlgebraicGeometry/MeromorphicDenominatorIdeal.lean` states
`AlgebraicGeometry.Scheme.Modules.meromorphic_denominator_ideal_nowhere_dense`.
Its sole theorem has proof `sorry`. The node statement is unchanged. Its statement dependencies
gain `def-sc-meromorphic-module`, whose accompanying module supplies the missing constructions.

Source read: Stacks [02P0](https://stacks.math.columbia.edu/tag/02P0), statement and entire proof;
[01X1](https://stacks.math.columbia.edu/tag/01X1), the paragraphs defining regular denominators,
meromorphic functions, and meromorphic modules; [01X4](https://stacks.math.columbia.edu/tag/01X4)
and [02OX](https://stacks.math.columbia.edu/tag/02OX). The local Stacks checkout is absent on
this machine, so these source pages were read online. The auxiliary module cites 01X4, the
actual general definition, rather than 02OW (which concerns reduced schemes).

Clause-by-clause correspondence:

- An arbitrary scheme is `X : Scheme.{v}`. No finiteness, separation, reducedness, or field
  assumption is imposed. The recorded `def-pc-scheme` Mathlib declarations were read in
  `Mathlib/AlgebraicGeometry/Scheme.lean` (Scheme at line 46, Hom at line 78).
- An invertible module is `L : X.Modules` with `[L.IsInvertible]`. This uses the dependency's
  exact recorded class `AlgebraicGeometry.Scheme.Modules.IsInvertible`, from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, whose field `exists_isoUnit` says
  locally isomorphic to the structure sheaf. Its full signature and docstring were read.
- The meromorphic module is `meromorphicModule X L`: the sheafification of localized sections,
  exactly the alternative defining presentation in Stacks 01X4. Its structure-sheaf case is
  `meromorphicModule X (unit X)`. The auxiliary statement `meromorphicModule_tensor_iso` records
  the equivalence with `K_X ⊗ L` for invertible L; the standard tensor product comes from the
  dependency's monoidal structure. This presentation is not a product of generic stalks and
  does not assume that all stalk denominators extend to a neighbourhood.
- The global section is represented by `s : unit X ⟶ meromorphicModule X L`.
  `SheafOfModules.unitHomEquiv` identifies such morphisms with compatible sections, and a
  compatible section on the Zariski opens is determined by its value on the top open. Thus this
  represents every global meromorphic section, with no additional data or condition.
- Regularity is exactly `hs : Mono (meromorphicSectionMap X L s)`. The map has domain K_X,
  not O_X. It is the unique O_X-linear extension of s through O_X → K_X; locally it sends
  a/b to as/b, so it is the canonical K_X-linear multiplication map. Its existence and
  uniqueness are separately named in the auxiliary module, with proof postponed.
- The sheaf I is `CategoryTheory.Limits.pullback s (toMeromorphicModule X L)`. Its projections
  `i` and `j` are the inclusion into O_X and multiplication by s into L. The first conjunct
  spells out, on EVERY open V, the exact defining set: f is in the image of i iff there is
  a section t of L with `toMeromorphicModule t = s(f)`. Since s is O_X-linear, s(f) is f times
  the restricted global section. Thus the pullback is not an arbitrary ideal assumed to have
  the required properties.
- Clause (1): `∀ x, ∃ U, x ∈ U ∧ IsAffineOpen U` supplies the affine neighbourhood, with
  A = Γ(X,U), whose spectrum identifies with this affine open. The quantified isomorphism
  `e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)` is precisely a sheaf
  trivialization over U, not merely an isomorphism of global section modules. The recorded
  upstream `sectionsLinearEquivOfOverIsoUnit e le_rfl` converts the scalar numerator a into
  the corresponding section of L. The next two predicates put a and b in the non-zero-divisors
  of A. The denominator b is also in the existing stalkwise-regular submonoid, as required to
  form the presheaf fraction. For affine U these two regularity descriptions coincide.
  `meromorphicFraction ... (LocalizedModule.mk ... b) = Hom.app s U (1 : Γ(X,U))` is the
  stated fraction representation. Finally the equivalence for EVERY y identifies I(U) with
  `{y | ∃ z, y*a = z*b}`. Since b is regular, this is exactly `{y | y(a/b) ∈ A}` in Q(A).
  No equality K_X(U) = Q(A) on all affine opens is assumed.
- Clause (2) is `SheafOfModules.IsQuasicoherent I`. Together with `Mono i` into O_X, the
  O_X-module structure makes this a quasi-coherent sheaf of ideals.
- Clause (3) is `Mono i ∧ Mono j` and the two separate existential sets Z. Each has
  `IsClosed Z ∧ IsNowhereDense Z`, and the appropriate cokernel's abelian-group stalk is
  `Subsingleton` at every x outside Z. A module stalk is zero exactly when its additive
  group is subsingleton, so these are precisely the two claimed support containments.

Dependency declarations used: `AlgebraicGeometry.Scheme` and its affine-open API (Mathlib),
`AlgebraicGeometry.Scheme.Modules.IsInvertible` and the monoidal structure
(`WeilConjectures.AlgebraicGeometry.Modules.Invertible`), and the new meromorphic-module
module. Further existing APIs used are `SheafOfModules` (Mathlib.Algebra.Category.ModuleCat.Sheaf),
`PresheafOfModules.sheafification` and `.sheafificationAdjunction`
(Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification), and the upstream
`AlgebraicGeometry.Scheme.Modules.sectionsLinearEquivOfOverIsoUnit`
(WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf, lines 175–187). The full signatures
and docstrings of these declarations were read. The principal-open density lemma is used
only by the natural-language proof, and is not an import needed to state this theorem.

Edge cases checked before finalizing the statement: the empty scheme (the neighbourhood
conclusion is vacuous, both support bounds can use the empty set); the zero ring on an empty
open (its localizations and section modules are subsingletons, not excluded); nilpotents and
embedded associated points (regular means non-zero-divisor, never merely nonzero); disconnected
and non-quasi-compact schemes (no finite affine cover is chosen); a regular section which is
already ordinary (b may be 1); and a trivial invertible module. No characteristic or dimension
bound is imposed. The stated universe v is arbitrary; the sheaf modules use the same universe
as the scheme, as do the project's recorded invertible modules.

Searches actually run (raw results and logged queries are in searches.jsonl):

- LeanFinder: "quasi coherent denominator ideal of a regular meromorphic section of an
  invertible sheaf" returned eight affine fraction/basic-open declarations, no matching theorem.
- LeanSearch: "sheaf of meromorphic functions on a scheme" was unavailable (HTTP Internal
  Server Error); this is not counted as a negative match.
- Loogle: "SheafOfModules, IsInvertible" returned unknown identifier IsInvertible, no hits.
- msearch grep: "Meromorphic|meromorphic|TotalQuotient", AlgebraicGeometry, returned no hits.
- A broader LeanFinder query "sheafification of localization of module sections at functions
  that are non zero divisors at all stalks meromorphic module" returned
  `TopCat.Presheaf.totalQuotientPresheaf`, among affine Tilde declarations. The entire
  Mathlib.Topology.Sheaves.CommRingCat source was then read. Its
  `submonoidPresheafOfStalk` (line 117) already provides the exact denominator submonoid and
  its restriction property; the final module reuses it, without a private definition.
  `totalQuotientPresheaf` (line 132) is the presheaf of rings, not the associated sheaf of
  modules for L, so it does not supply the missing declaration.
- msearch grep: "submonoidPresheafOfStalk|totalQuotientPresheaf|meromorphic", Topology/Sheaves,
  confirmed these five hits. Loogle "LocalizedModule" returned the existing localization
  type and operations, which the construction uses directly.
- rg of WeilConjectures and lean/Sheaf for meromorphic/Meromorphic/denominator/Denominator
  found no meromorphic-module or denominator-ideal theorem; the hits concerned unrelated
  denominator clearing and rational functions. The exact node-id grep in WeilConjectures
  found nothing. Searches of dag/lean_names_upstream.json and of the full source trees for
  the proposed declaration names found no collisions.
- DAG keyword/tag searches found the existing statement nodes about generic-stalk products
  and existence of regular sections, but no definition node for meromorphic modules.
  `blueprint_refs.py search 'meromorphic'` and `'meromorphic section'` both found zero
  blueprint nodes. The denominator query found six unrelated units/lemmas, none defining
  this notion. `blueprint_refs.py ancestor` identified lem-sc-hilbert-polynomial.

No statement correction or disputed statement. No dependency module replaces an existing
record. All theorem proofs, including construction well-definedness obligations, are `sorry`;
no definition has `sorry` as data. The named obligations are
`exists_meromorphicRestriction`, `meromorphicRestriction_id`, `meromorphicRestriction_comp`,
`meromorphicLocalization_natural`, `meromorphicModule_tensor_iso`, and
`exists_meromorphicSectionMap`. Their docstrings supply natural-language proofs and the new
node id. Restriction maps and the section extension use the specified localization universal
property; choices are constrained by their exact values on every fraction or by uniqueness,
rather than selecting unspecified objects.

## New nodes

`def-sc-meromorphic-module` defines the sheafification of localized module sections, its
canonical ordinary-section and fraction maps, and the induced scalar map of a meromorphic
section, following Stacks 01X2, 01X4, and 02OX. Its own module is
`lean/Sheaf/AlgebraicGeometry/MeromorphicModule.lean`. The existing generic-stalk-product
nodes are assertions under extra finiteness/associated-point hypotheses, not this definition.
The Mathlib denominator submonoid and localization type are reused. The searches listed
above found no existing sheafified meromorphic module. The new node cites the existing
scheme, sheaf-of-modules, sheafification, and invertible-module definition nodes. It is attached
to the ancestor's denominator-ideal step, and the item cites it in stmt_deps.

## Second reading by C1

I reread the item node, its Stacks source (Tag 02P0, with definitions in Tags 01X2,
01X4, and 02OX), and both delivery modules. The correspondence is as follows.

- The scheme `X : Scheme.{v}` is the arbitrary scheme in the source; no noetherian,
  separated, reduced, finite type, or characteristic hypothesis is added.
- `L : X.Modules` with `[L.IsInvertible]` is the invertible sheaf. The section
  `s : unit X ⟶ meromorphicModule X L` is the global meromorphic section, and
  `Mono (meromorphicSectionMap X L s)` is exactly regularity (injectivity of
  multiplication by `s` on `K_X`).
- The local `let I := pullback s (toMeromorphicModule X L)` and its projections `i,j`
  render the source subsheaf `{f | fs ∈ L}`. The first displayed equivalence quantifies
  every open `V` and section `f`, so it states that defining condition rather than merely
  assuming an ideal with that property.
- The affine-neighbourhood clause quantifies every `x`, an affine `U`, a sheaf
  trivialization `e`, and fractions `a,b`; it requires both `a` and `b` to be
  non-zero-divisors and gives the fraction equality and the exact equation
  `∃ z, y*a = z*b`. This matches clause (1), including the total-fraction calculation.
- `IsQuasicoherent I ∧ Mono i ∧ Mono j` renders clause (2) and the two injectivity
  assertions in clause (3). The two final existential clauses quantify closed nowhere
  dense `Z` and subsingleton cokernel stalks outside `Z`, expressing both support bounds.

The auxiliary definition module was checked against its new definition node: it uses
Mathlib's stalkwise denominator submonoid, localization, and sheafification; it introduces
no private duplicate notion and has no hollow definition. Every postponed argument is a
named theorem with `sorry`. Searches recorded in the worker report found no existing
meromorphic-module or denominator-ideal declaration. The item now cites
`def-sc-meromorphic-module`, as required for the definitions used by its signature.

Edge cases remain covered: the empty scheme makes the neighbourhood statement vacuous;
empty or zero section rings are allowed; nilpotents use non-zero-divisors rather than
nonzero elements; disconnected and non-quasi-compact schemes require no finite cover;
`b = 1` handles an ordinary section; and the universe `v` is unrestricted. No mismatch
was found in the second reading, so no Lean statement repair was needed.
