## Worker report

The module `Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic` states
`AlgebraicGeometry.Etale.isZero_higherDirectImage_openImmersionLowerShriek_injective`.
Its only proof is `sorry`. There are no new definitions, dependency replacements,
or statement corrections. The original node is copied unchanged except for `lean`.

Hypotheses and clauses, individually:

- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The universe follows the existing six-functor coefficient convention; any small finite
  ring can be lifted to this universe. The zero ring is allowed.
- The four schemes are `{A B C D : Scheme.{u}}` with no extra properties.
- The top open immersion is `(k : A ⟶ B) [IsOpenImmersion k]`.
- The bottom open immersion is `(i : C ⟶ D) [IsOpenImmersion i]`.
- The left proper map is `(r : A ⟶ C) [IsProper r]`.
- The right proper map is `(p : B ⟶ D) [IsProper p]`.
- The equality pk = ir is `(hcomm : k ≫ p = r ≫ i)`, in Lean composition order.
- No Cartesian hypothesis is imposed: there is no `IsPullback` binder.
- The sheaf is `(J : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  This is the established six-functor encoding of constant-coefficient module sheaves,
  explicitly allowed in the dependency record for def-weil-pbc-etale-sheaves.
- Its injectivity is `[Injective J]` in that same module-sheaf category, not after forgetting
  coefficients.
- The extension by zero is `(openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J`.
- Its degree-zero embedding is `DerivedCategory.Plus.singleFunctor ... 0`.
- Derived pushforward is `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p`.
- All positive degrees are `(q : ℤ) (hq : 0 < q)`; `homologyFunctor ... q` takes the
  cohomology sheaf. The conclusion `IsZero (...)` expresses precisely R^q p_*(k_! J) = 0.
  Using integer degrees does not impose or remove any positive degree.

Dependency declarations and imports:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and its morphisms,
  `Mathlib.AlgebraicGeometry.Scheme`.
- def-weil-open-immersion: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- def-weil-proper-morphism: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- def-weil-pbc-etale-sheaves: `CategoryTheory.Sheaf`, applied to the small etale topology
  and `ModuleCat`, with the existing six-functor encoding noted in its record;
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` is imported as recorded.
- def-sp-injective-resolutions: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- def-weil-pbc-extension-by-zero: `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- def-weil-pbc-direct-image: `AlgebraicGeometry.Etale.lowerStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, whose actual source is
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  The latter source was read: it is exactly `lowerStar.rightDerivedFunctorPlus`.

Recorded proof-dependency modules are imported without `public`: module/abelian derived
comparison, pullbacks, closed immersions, clopen sheaf products, open-extension stalk formulas,
geometric-stalk conservativity, bounded-below right derivation, and torsion assembly.
The proper geometry and extension-by-zero adjunction proof imports coincide with public
statement imports. The nodes sbc-prop-extension-by-zero-and-arbitrary-base-change and
lem-kun-stalks-of-cohomology have no recorded Lean modules, so cannot yet contribute imports.
The docstring preserves the full seven-step proof plan, including the module/abelian
comparison and the clopen injectivity argument; it never assumes abelian injectivity of J.

Source and edge cases checked:

Read Stacks `more-etale.tex`, lemma-shriek-proper-and-open (0F7B), especially the case (b)
claim for injectives. The original source also imposes commutativity but not Cartesianity.
The open-immersion specialization satisfies its separated locally-quasi-finite hypotheses.
A finite ring is torsion, as the node explains. No extra geometric assumptions are needed.
For empty A, extension by zero is zero. Empty B forces empty A; empty C forces empty A;
empty D forces all schemes empty. Each gives zero as expected. The zero sheaf and zero ring
also give zero. With identity horizontal immersions this is ordinary higher-direct-image
vanishing on injectives. A proper non-surjective clopen inclusion A into B over C = D
shows why no Cartesianity or equality A = B ×_D C should be added. Degree zero is deliberately
excluded: even identity maps and a nonzero injective sheaf need not give zero there.
All universes and variables are explicitly bound; there are no local definitions or notation.
No STATEMENT-DISPUTED or mathematical node fault was found.

Searches performed before writing:

- `msearch.py ... leanfinder`: “Open extension of an injective etale module sheaf has zero
  higher direct images in a commutative proper open square”. Eight results were generic
  injectivity, local injectivity, or generic derived vanishing, not this square statement.
- `msearch.py ... loogle`: `openImmersionLowerShriek, rightDerivedLowerStarPlus` returned
  zero hits, reporting the upstream identifier unknown to its index.
- `msearch.py ... grep`: `extensionByZero|lowerShriek.*acyclic|acyclic.*lowerShriek`
  returned zero hits in Mathlib.
- `msearch.py ... leansearch`: the full commutative proper/open injective acyclicity query
  returned service unavailable (Internal Server Error); no verdict is inferred from that.
- `rg` of the upstream WeilConjectures source and `lean/Sheaf`, plus the upstream-name index,
  for the item id, open-extension acyclicity and zero/open-extension patterns found no exact
  statement. The nearby `OpenImmersionLowerShriekLowerStarExchange` was read: it concerns a
  Cartesian square and a derived exchange map, so it is not an existing statement of this node.
- The proposed full declaration name was searched in Mathlib, upstream WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`; there were no collisions.

Validation: the delivered module compiles cleanly through `scompile.py`, on the server,
with nice 19, two threads and a 60-second limit (reported compilation time 1.6 seconds).
The required delivery dry run is run after writing this report; no delivery is pushed.

## Second reading by NQ

Independent reading of the original DAG node, the sandbox node and Lean module,
Stacks `more-etale.tex` section “Preliminaries to derived lower shriek via
compactifications”, Tag 0F7B, and the dependency records and declarations.
No mathematical or signature mismatch was found; the Lean and node are unchanged.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. This is a ring, not a field, and imposes no invertibility condition.
2. Four arbitrary schemes: `{A B C D : Scheme.{u}}`. Mathlib `Scheme` is a locally
   ringed space with affine neighbourhoods, as def-pc-scheme requires.
3. Top open immersion: `(k : A ⟶ B) [IsOpenImmersion k]`.
4. Bottom open immersion: `(i : C ⟶ D) [IsOpenImmersion i]`. The dependency's
   `IsOpenImmersion` is the locally-ringed-space open-immersion property.
5. Left proper morphism: `(r : A ⟶ C) [IsProper r]`.
6. Right proper morphism: `(p : B ⟶ D) [IsProper p]`. Mathlib proper means separated,
   universally closed and locally finite type; universal closedness supplies
   quasi-compactness, so this is the node's finite-type properness.
7. Commutativity: `(hcomm : k ≫ p = r ≫ i)` renders precisely pk = ir.
   There is no pullback or Cartesian assumption, nor any hidden surjectivity.
8. Every small-etale module sheaf: `(J : Sheaf A.smallEtaleTopology
   (ModuleCat.{u + 1} Λ))`. The dependency record explicitly permits this
   six-functor encoding alongside constant-ring `SheafOfModules`.
9. Injectivity: `[Injective J]`. I read `CategoryTheory.Injective.factors`:
   it is extension across every monomorphism in this module-sheaf category.
   No injectivity of the underlying abelian sheaf is assumed.
10. Extension by zero: `(openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj J`.
    I read its upstream definition via `localizationLowerShriek` and its
    restriction adjunction: this is the dependency's extension by zero.
11. Higher direct images: embed this sheaf using `Plus.singleFunctor ... 0`,
    apply `rightDerivedLowerStarPlus ... p`, then `Plus.homologyFunctor ... q`.
    I read `lowerStar` (sections on the base-change etale object),
    `rightDerivedLowerStarPlus` (its bounded-below right derived functor), and
    both Mathlib Plus functors. They give exactly the node's R^q p_*.
12. Vanishing in every positive degree: `(q : ℤ) (hq : 0 < q)` and `IsZero`
    of that cohomology sheaf. Quantifiers range over every J and every positive q;
    there is no extra conclusion or hypothesis.

Source check: Tag 0F7B assumes a commutative square with proper vertical maps
and separated locally quasi-finite horizontal maps, with no Cartesianity.
Its case (b) explicitly states the injective acyclicity claim used here.
Open immersions satisfy the horizontal hypotheses, and a finite coefficient ring
is torsion. No section-wide Noetherian, characteristic, or base-field hypothesis
is present. The node legitimately specializes that source; no correction is needed.

Edge cases: empty A, B, C or D remain admitted, with the forced empty sources
and zero extensions. The zero ring and zero module sheaf remain admitted.
Degree zero is correctly excluded (identity maps and a nonzero injective give a
nonzero degree-zero image). Every positive natural degree is a positive integer
and conversely; no degree is lost. There is no index-family restriction.
The explicit universe `u` ranges freely, with the established site/module universe
shift; finite rings of smaller size can be lifted, and no independent test-object
universe makes a hypothesis vacuous. All variables and universes are bound.

Independent searches used different phrasing from the author:

- LeanFinder: “Proper pushforward of extension by zero of injective coefficients
  in a noncartesian open square has vanishing positive cohomology”. Eight generic
  K-injectivity, derived-Hom vanishing and Mayer–Vietoris hits; none is this result.
- Loogle: `"rightDerived", "Injective"`. Twelve generic right-derived-on-injective
  statements, which require injectivity of the input itself; none asserts this
  open-extension acyclicity.
- msearch grep: `higherDirectImage.*open|open.*acyclic|shriek.*vanish`: no hits.
- Direct rg across Mathlib, upstream WeilConjectures and project lean/Sheaf:
  `shriek.*(acyclic|injective)|(?:acyclic|injective).*shriek|isZero_higherDirectImage_openImmersion`.
  I opened the nearby project `etale_lower_shriek_to_lower_star_injective`
  (injectivity of a comparison morphism for finite etale maps), and the upstream
  `openImmersionLowerShriekLowerStarExchange` signature (a Cartesian-square derived
  exchange map). Neither says the node's statement. The pro-etale hits concern
  a different site. No existing exact declaration was found.

No new nodes or dependency replacement modules occur in this delivery.
There are no definitions, hollow data, local notation, local instances or proved
lemmas. The sole theorem has `sorry`; its source/blueprint docstring reproduces all
seven proof steps, including the essential module/abelian comparison and clopen
injectivity argument. Public imports serve the statement; ordinary imports serve
recorded proof dependencies. I checked that `lean.statement` equals the signature
verbatim. The independent server scompile passed cleanly in 1.6 seconds with
nice 19, two threads and the unchanged 60-second limit.

Changes in this reading: appended this independent review only; no Lean or DAG
changes were warranted.
