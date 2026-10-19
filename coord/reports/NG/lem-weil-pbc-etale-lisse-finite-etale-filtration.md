## Worker report

The module `Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration` states
`AlgebraicGeometry.Etale.exists_lisse_finiteEtale_filtration`, with its sole proof `sorry`.
It introduces no definition, auxiliary theorem, or new node. The natural statement is
unchanged. The declaration docstring carries all ten steps of the node's proof.

Hypothesis and conclusion correspondence:

- The affine scheme X = Spec A is literally `Spec (.of A)`, with `A : Type u`,
  `[CommRing A]` and `[IsNoetherianRing A]`. Thus there is no extra nonemptiness,
  irreducibility, geometric unibranchness, or characteristic hypothesis.
- The finite commutative coefficient ring is `Λ : Type (u + 1)` with `[CommRing Λ]`
  and `[Finite Λ]`, following the project's module-valued étale sheaf convention.
- The module sheaf is `F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat Λ)`.
  `[Scheme.IsFiniteLocallyConstantSheaf F]` asserts étale local constancy and finitely
  generated geometric stalks, which over the finite ring Λ are exactly finite module
  fibres. The full signature and docstrings of `IsLocallyConstantSheaf`,
  `LocallyConstantDatum`, `IsFiniteSheaf` and `IsFiniteLocallyConstantSheaf` were read.
- `ℓ n : ℕ`, `hℓ : ℓ.Prime`, `hn : 1 ≤ n`, and `hF : (ℓ ^ n) • 𝟙 F = 0`
  render the prime, positive exponent, and annihilation assumptions. The last equality
  says multiplication by ℓ^n is the zero endomorphism of the module sheaf.
- Existential `T : Scheme`, `g : T ⟶ Spec (.of A)` and the conjunction
  `IsFinite g ∧ Etale g ∧ Surjective g` give the required finite étale surjection.
- `d : ℕ`, `1 ≤ d` and `¬ ℓ ∣ d` give its positive prime-to-ℓ degree.
  Every algebraically closed field Ω in the scheme universe and every geometric point
  `s : Spec Ω ⟶ Spec A` satisfy `Nat.card (g.GeometricFiber s) = d`.
  Finiteness of these lift sets follows from `IsFinite g`; hence cardinality cannot
  accidentally describe an infinite fibre. `GeometricFiber` is the recorded canonical
  subtype of lifts, not a replacement notion of degree.
- `k : ℕ`, `U : Fin k → T.Opens` give the finite family of open subschemes.
  `IsAffineOpen (U a) ∧ IsClosed (U a : Set T)` makes each affine and clopen;
  `Pairwise ... Disjoint` and the union equality give precisely a disjoint cover of T.
  Open subschemes with disjoint covering images express the finite scheme coproduct.
- For each a, `r : ℕ`, `c : Fin (r + 1) → Subobject ...` and `hc : Monotone c`
  give an increasing finite filtration by module subsheaves of the specified restriction.
  Its ambient object is the canonical `upperStar` along g followed by the open inclusion
  `(U a).ι`. Endpoints `IsZero (c 0 : Sheaf ...)` and `c (Fin.last r) = ⊤` give zero
  and the whole sheaf. IsZero is equivalent to the initial subobject being bottom.
- For each `i : Fin r`, `cokernel (Subobject.ofLE (c i.castSucc) (c i.succ) ...)`
  is the quotient of consecutive subsheaves. Its isomorphism to
  `(constantSheaf (U a).toScheme.smallEtaleTopology (ModuleCat Λ)).obj M`
  for some `M : ModuleCat Λ` with `Finite M` gives exactly the constant finite-module
  graded piece. No freeness or rank-one condition is imposed.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (every ideal finitely generated).
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom` / affine-open conventions;
  the hypothesis uses the literal spectrum, rather than a separate affine predicate.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` / `Scheme.Etale`.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.IsFiniteLocallyConstantSheaf`,
  extending `IsLocallyConstantSheaf` and `IsFiniteSheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`:
  `Scheme.Hom.GeometricFiber`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.CategoryTheory.Subobject.Limits`: the existing subobject order and terminal endpoint;
  `Subobject.ofLE` gives the canonical inclusion between comparable subobjects.

The module-valued encoding is the constructible-sheaf encoding expressly allowed in
`def-weil-pbc-etale-sheaves`; its set-valued predicates are not incorrectly applied to
modules. The recorded EtaleSheaves source was missing in the old local checkout, so
it was read with `scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
All available recorded proof-dependency modules are imported as proof imports; the
Mathlib matches are supplied by their respective Mathlib modules.

Edge cases checked before writing: the empty spectrum permits T empty, d = 1 and k = 0;
no geometric point exists there, so the fibre assertion is vacuous. For F zero one can
use a length-zero filtration, since bottom and top subobjects then agree. Repeated
filtration terms and zero constant quotients are allowed. The zero coefficient ring
is permitted. The prime need not be invertible on the base. A disconnected base is
covered by finitely many affine clopens and repeating component covers gives common
degree. No chosen geometric base point or connectedness assumption is imposed.

Searches for an existing statement:

- `msearch.py ... leanfinder "finite primary locally constant module sheaf admits prime
  to p finite etale cover with filtration by constant modules"`: eight unrelated hits
  (étale ring algebras, rank-at-stalk and local cohomology), no matching theorem.
- `msearch.py ... loogle "IsFiniteLocallyConstantSheaf, Etale, IsFinite"`: zero hits,
  unknown identifier IsFiniteLocallyConstantSheaf in the Mathlib search service.
- `msearch.py ... grep "filtration|Filtered" AlgebraicGeometry`: nine hits on filtered
  colimits and étale points, none on this finite étale filtration theorem.
- `rg` in upstream WeilConjectures and project `lean/Sheaf` for the item id, local
  constancy, finite étale reduction and filtration/constant patterns: the upstream
  `ConstructibleSheaf.LocallyConstantReduction.exists_finite_etale_reduction` and
  project's `ConstructibleSheaf.LocallyConstantCoverFiltration` cover only prime-field
  coefficients and irreducible bases. Their full signatures were read; neither matches
  the finite-ring, primary-power, affine possibly disconnected statement here.
  The item-id search finds only a proof-plan reference in LisseOpenRelativeLineConstructibility.
- Inspected existing subobject filtrations in CoherentFiltrationIntegralSubschemes and
  IntegralIdealComparisonFiltrations; reused Mathlib's subobjects and cokernels directly.

Sources read: Stacks `etale-cohomology.tex`, lemma-pullback-filtered-modules (0GJ0),
lemma-locally-constant-on-connected (0DV5), especially its finite-ring clause (3).
The node's finite-ring variant follows 0DV5, as its source and proof explicitly state.
No statement dispute or correction was needed.

Validation uses only `scompile.py` and the prescribed delivery dry run. The initial
elaboration exhausted typeclass heartbeats synthesizing the bottom subobject. Increasing
the heartbeat budget led to a 60-second timeout. The final signature uses the equivalent
`IsZero` condition on the initial subobject instead, with the default typeclass budget
and the unchanged 60-second file limit. Every variable and universe is explicitly bound.


## Second reading by NG

I independently opened the delivered node, its full ten-step proof, its Lean module,
all ten statement-dependency nodes and their recorded interfaces. I read Stacks
etale-cohomology.tex, lemma-locally-constant-on-connected (0DV5), including its
hypotheses and finite-ring clause (3), lemma-action-l-group (0GIZ), and
lemma-pullback-filtered-modules (0GJ0), including their proofs. The node explicitly
uses the finite-ring variant of 0GJ0: 0DV5 (3) applies on connected schemes without
geometric unibranchness. No missing standing hypothesis must be imported from the
irreducible geometrically unibranch formulation of 0GJ0. Finite clopen assembly and
repetition of component covers give the node's constant global degree.

My inventory of the node, with its Lean rendering and verdict:

1. Object X = Spec A, A commutative Noetherian: `(A : Type u) [CommRing A]
   [IsNoetherianRing A]`, with X literally `Spec (.of A)`. Exact; no field,
   connectedness, reducedness, nonemptiness or separation assumption is added.
2. Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. Exact, including the zero ring.
3. Module sheaf on the small etale site: `F : Sheaf (Spec (.of A)).smallEtaleTopology
   (ModuleCat.{u + 1} Λ)`. Exact under the explicitly authorized module-valued
   encoding in def-weil-pbc-etale-sheaves, whose live source I also obtained using
   `scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
4. Etale local constancy and finite module fibres:
   `[Scheme.IsFiniteLocallyConstantSheaf F]`. Exact. I opened upstream
   ConstructibleSheaf/Defs.lean: LocallyConstantDatum is a jointly surjective etale
   cover whose localized sheaves are constant; IsFiniteSheaf requires finitely
   generated geometric stalks; IsFiniteLocallyConstantSheaf extends both. Over the
   finite ring these stalks are finite sets. Separably closed stalk tests are the
   standard equivalent formulation of the geometric finiteness condition.
5. Prime ell, positive n, annihilation: `(ℓ n : ℕ) (hℓ : ℓ.Prime)
   (hn : 1 ≤ n) (hF : (ℓ ^ n) • 𝟙 F = 0)`. Exact: scalar multiplication of the
   identity in this additive category is multiplication on the module sheaf.
6. Finite etale surjection: existential `T : Scheme.{u}`, `g : T ⟶ Spec (.of A)`
   with `IsFinite g ∧ Etale g ∧ Surjective g`. Exact; these are the canonical
   scheme-morphism properties, not additional structure imposed on the base.
7. Positive prime-to-ell common degree: existential natural `d`, `1 ≤ d`,
   `¬ ℓ ∣ d`, followed by the universal algebraically closed field and geometric
   point test `Nat.card (g.GeometricFiber s) = d`. Exact. I opened GeometricFiber:
   it is precisely the subtype of lifts with composite s. Its finite-morphism
   instance ensures Nat.card cannot use its infinite-type convention here.
8. Finite disjoint affine clopen decomposition of T: `k : ℕ`, `U : Fin k → T.Opens`,
   `IsAffineOpen (U a) ∧ IsClosed (U a : Set T)`, pairwise disjointness and union
   equal to Set.univ. Exact: the open subschemes of a disjoint covering are the
   summands of the scheme coproduct. No nonempty-summand condition is required.
9. The sheaf to be filtered is exactly the restriction of g inverse image F:
   `((upperStar (ModuleCat Λ) (U a).ι).obj ((upperStar (ModuleCat Λ) g).obj F))`.
   Exact. I opened the recorded upperStar definition: left Kan extension along
   site base change followed by sheafification, with the recorded adjunction.
   Applied in ModuleCat, this is module inverse image, not an arbitrary map.
10. Finite increasing filtration by module subsheaves: existential `r : ℕ`,
    `c : Fin (r + 1) → Subobject ...`, and `hc : Monotone c`. Initial endpoint
    `IsZero (c 0 : Sheaf ...)` is equivalent to the zero subobject; terminal
    endpoint `c (Fin.last r) = ⊤` is the entire specified sheaf. Exact.
11. Each successive quotient is constant with finite module value: for each
    `i : Fin r`, `cokernel (Subobject.ofLE (c i.castSucc) (c i.succ) ...)` is
    isomorphic to `(constantSheaf ... (ModuleCat Λ)).obj M` for some M with
    `Finite M`. Exact. I opened Subobject.ofLE and its Mono instance and the
    constantSheaf definition. The cokernel is the quotient of these consecutive
    subobjects; no freeness, cyclicity or rank-one condition is added.
12. Quantifier order: first T and g, then the single d for every geometric fibre,
    then one finite clopen family, then each summand's length and chain, then
    each step's finite module. Exact; none depends on a later geometric point.

Other dependency signatures checked in the pinned Mathlib: Scheme extends
LocallyRingedSpace with local affine charts; IsNoetherianRing is IsNoetherian R R;
IsAffineHom tests affine-open preimages; smallEtaleTopology is the topology on the
etale over-category; constantSheaf is sheafification of Functor.const. No private
copy of a dependency, new definition node, or dependency module occurs here.

Edge cases: A may be the zero ring, so the empty spectrum is covered by T empty,
d = 1 and k = 0. The empty family really is allowed (`Fin 0`). For the zero sheaf,
r = 0 has a single chain term, simultaneously zero and top, and no quotient tests.
Repeated filtration terms and zero quotient modules are permitted. n = 0 is excluded
exactly as in the node; all prime characteristics of the base are allowed and there
is no invertibility assumption on ell. The coefficient ring can be zero. A disconnected
base is allowed and the common degree can be obtained by repeating component covers.
All universes are bound: schemes and geometric fields have universe u; coefficients
and module carriers have u+1 as required by the existing small-site API. Finite rings
and finite module values can be lifted to this universe. Tests include algebraic
closures of residue fields in u, so no point is lost through a smaller test universe.
There is no independent restrictive index universe: the families are finite.

Independent searches, with different wording from the first worker:

- LeanFinder via msearch: "A locally constant finite torsion module sheaf has a
  prime-to-ell finite etale cover with constant successive quotients". Eight hits,
  on etale algebras, finite fibres and condensed modules; no matching theorem.
- Loogle via msearch: `Subobject, CategoryTheory.Limits.cokernel`. No hits; the
  service reports unknown identifier Subobject. I therefore inspected the actual
  Mathlib Subobject source directly rather than interpreting this as absence.
- Grep via msearch: `locally.constant|[Ff]iltration`, AlgebraicGeometry. Four hits
  in FlatRank about locally constant rank; no matching statement.
- Independent rg over upstream WeilConjectures, project lean/Sheaf and Mathlib's
  AlgebraicGeometry for prime-to-cover/degree and constant-filtration patterns.
  I opened both exists_finite_etale_reduction and exists_finite_etale_cover_filtration
  completely. They require an irreducible base and prime-field coefficients and
  yield prime-field graded pieces; neither states this node. Other hits concern
  trace transfers, generic curve reductions or topological constant subsheaves.

No mathematical mismatch was found. I changed no correct Lean or node text; the
only change is this independent review record. The sole theorem has the whole
proof `sorry`; no definition is hollow and no theorem was proved. The declaration
docstring follows each of the ten node proof steps and carries the required source
and blueprint identifier. There is no statement_change and no citer audit is needed.
The stored lean.statement equals the file's signature verbatim, every Lean line has
at most 100 characters, and there are no unbound variables or universes.

Validation: the prescribed scompile.py wrapper compiled the sole delivered file
cleanly (library compile 2.5 seconds), with no errors or warnings. An initial invocation
from the read-only checkout used a relative path absent there; rerunning from this
sandbox resolved that path and completed successfully. No direct compiler or global
build was run. Delivery dry-run and actual delivery follow this review.
