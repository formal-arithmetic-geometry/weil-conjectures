## Worker report

The module `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients` states
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`.
Its sole proof is `sorry`; it defines no new notion and changes only the item's `lean` record.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`.
- The finite ring A is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Commutativity is exactly the cited coefficient conventions, as the stage-1 split report
  explicitly confirms; no nonzero-ring assumption is imposed.
- An annihilator invertible in k is `(N : ℕ)` and
  `hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k))`. Unfolding the recorded
  definition gives `0 < N`, finiteness, `(N : A) = 0`, and invertibility of the constant
  section N on Spec k. The latter is equivalent to invertibility in k. Equality on the
  unit of A is equivalent to annihilating every A-module. Choosing a positive natural
  annihilator loses no integer case, since a nonzero integer can be replaced by its
  absolute value; zero is never invertible in a field.
- Finite-type k-schemes and their open immersion are `{X Y : Scheme.{u}}`,
  `aY : Y ⟶ Spec (.of k)`, `[LocallyOfFiniteType aY] [QuasiCompact aY]`,
  and `j : X ⟶ Y` with `[IsOpenImmersion j]`. The k-structure on X is j followed by aY.
  Y is noetherian, so this open immersion is quasi-compact and X is automatically of
  finite type over k. This is the same redundant-X-hypothesis elimination explained by
  the upstream corollary's docstring. Every open immersion between finite-type k-schemes
  is covered, and no separatedness is assumed.
- The input `K ∈ D^b_c(X,A)` is `K : DerivedCategoryModule A X` with
  `hK : DerivedCategory.isBoundedConstructible A X K`.
- The conclusion is `DerivedCategory.isBoundedConstructible A Y` applied to
  `(rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj K`. This asserts both
  constructibility of every cohomology sheaf and vanishing outside some finite interval.
  The derived category is ordinary; there is no Tor-amplitude condition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, using the recorded
  finite-stratification constructibility predicate, and its full subcategory.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, through the coefficient convention module:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the actual abbreviation is in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`) and ordinary derived cohomology.
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `def-weil-pbc-scheme-conventions` has no declaration: its record explicitly collects
  Mathlib scheme and morphism properties. The statement uses `Scheme`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsOpenImmersion`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, the recorded pushforward. Its ordinary total
  right derived functor is the existing `AlgebraicGeometry.Etale.rightDerivedLowerStar`
  from `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  The recorded bounded-below variant is not the ambient category of this node.

Proof-only imports retain every available recorded proof-dependency module, including
constructible kernels/cokernels, comparison with abelian coefficients, left exactness,
enough injectives, long exact sequences, Grothendieck abelian categories, bounded-below
injective representatives and the truncation spectral sequence. The prime-field
corollary `cor-fin-deligne-open-over-field` has no Lean record and is not imported.
The theorem docstring reproduces all six steps of the node's proof.

Edge cases checked: A = 0 and N = 1 are allowed; empty X and empty Y are allowed;
no connectedness, perfection or algebraic closure of k is assumed; coefficients may
have mixed prime powers and need not be a prime-field algebra; K may have negative
cohomological degrees and need not have finite Tor amplitude. The coefficient universe
is the prescribed u+1; no independent too-small test universe is introduced.

Searches performed:

- msearch LeanFinder: "Open direct image preserves bounded constructible etale complexes
  with finite coefficients over a field". Eight hits concern constructible subsets and
  etale loci, not this sheaf-theoretic finiteness statement.
- msearch Loogle: `"constructible"`. Twelve topological constructibility hits; no match.
- msearch grep of Mathlib: `boundedConstructible|isBoundedConstructible`. No hits.
- msearch LeanSearch: "Open immersion derived direct image of finite coefficient bounded
  constructible etale complexes over a field". Service unavailable (Internal Server Error).
- rg of upstream WeilConjectures and side lean/Sheaf for this node ID and bounded
  constructible lower-star/open finite-coefficient names found the upstream
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`
  in `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage`.
  Its full signature and docstring were read. It uses the source's
  `DerivedCategory.boundedConstructible`, based on `Scheme.IsConstructibleSheaf`,
  rather than the recorded dependency's `isBoundedConstructible`, based on
  `Scheme.IsConstructibleEtaleModuleSheaf`. The two predicates require a stage-3 bridge;
  this is precisely the distinction documented by the bounded-constructible dependency's
  reviewed record. Thus that declaration is not an exact existing match.
- The same rg search found no side-project declaration of this statement. The existing
  derived pushforward and coefficient conventions are reused, with no private copies.

Validation: the first scompile.py invocation lost its SSH connection before compiling.
The retry succeeded: the delivered module compiled in 1.5 seconds, with no errors or
warnings, nice 19, two threads, 60 seconds per file. The private overlay also compiled
SmoothBaseChangeCoefficients (1.4 s) and EtaleConstantModuleDirectImageLeftExact (9.2 s).
No local compile was attempted.
There is no statement correction, disputed mathematical assertion, new node or
replacement dependency module.

## Second reading by NN

I independently read the node, its blueprint source at
sec-smooth-purity/sk-prop-sf-cbc/cor-fin-deligne-open-finite-coefficients.md,
the module, and all five statement dependencies and their recorded declarations.
The node's source is the blueprint, not a Stacks theorem with additional standing
hypotheses. I also read Stacks 03FD, 0D6J(3), 03RZ and 015B in the local TeX sources:
the coefficient comparison allows ringed sites, the Serre assertion requires a
Noetherian coefficient ring (automatic for finite A), and the long exact sequence
requires enough injectives and a left exact functor. These add no hypotheses here.

Object, hypothesis and conclusion checklist, in the node's order:

1. A field k: `(k : Type u) [Field k]`. Exact; no algebraic closure, separable
   closure, perfection or characteristic restriction on the field itself.
2. A finite coefficient ring A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
   Exact under the explicitly cited sbc-def-coefficient-conventions, whose node
   specifies commutative coefficients. The bounded-constructible dependency also
   specifies a finite commutative ring. This does not silently specialize an
   arbitrary noncommutative coefficient convention.
3. An integer annihilator invertible in k: `(N : ℕ)` and
   `hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k))`. I opened this definition:
   it is `0 < N ∧ Finite A ∧ (N : A) = 0 ∧ IsUnit (N : Γ(Spec (.of k), ⊤))`.
   Global sections of Spec k identify with k, so the final clause is the required
   invertibility. Any allowed integer can be replaced by its positive absolute
   value; zero is not invertible in a field. Quantifying over every such witness
   rather than existentially assuming one is an equivalent presentation here,
   because neither K nor the conclusion depends on N. Exact.
4. Finite-type k-schemes X and Y: `{X Y : Scheme.{u}}`,
   `(aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]`.
   These two Mathlib morphism classes are precisely finite type. Y is Noetherian;
   every open subscheme is quasi-compact and locally of finite type over k.
   Thus the k-structure `j ≫ aY` on X is automatically finite type. Conversely,
   given the node's open immersion of k-schemes, its X-structure is this composite.
   There is no missing finite-type or compatibility hypothesis and no additional
   separatedness assumption. Exact.
5. The open immersion: `(j : X ⟶ Y) [IsOpenImmersion j]`, the collected scheme
   conventions' actual Mathlib notion. Exact.
6. Every bounded constructible K: `(K : DerivedCategoryModule A X)` and
   `(hK : DerivedCategory.isBoundedConstructible A X K)`. I read DerivedCategories,
   the upstream DerivedCategoryModule abbreviation, BoundedConstructibleComplexes,
   and IsConstructibleEtaleModuleSheaf. The ambient category is the ordinary
   derived category of `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
   The hypothesis says that every integer cohomology sheaf has a finite
   constructible locally closed stratification with finite constant module
   trivializations, and vanishes outside some integer interval. Exact.
7. Rj_*K belongs to D^b_c(Y,A): the conclusion applies that same predicate at Y to
   `((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj K)`. I opened lowerStar
   in UpperLowerStar.Defs (objectwise base-change pushforward) and
   rightDerivedLowerStar in Derived.UpperLowerStarCoherence (its total ordinary
   right derived functor). Both constructibility and boundedness are asserted,
   with original A-coefficients, no specified bound and no Tor-amplitude condition.
   Exact; the bounded-below variant would not be the displayed ambient category.

Edge cases: the zero ring is allowed, with N = 1; the zero complex and empty X
or Y are allowed. No nonempty stratum, index set or scheme hypothesis occurs.
There is no degree-zero truncation: negative cohomological degrees are covered.
N = 0 is excluded exactly because it cannot be invertible in k. In characteristic
p > 0, hA excludes precisely annihilators divisible by p; mixed prime-power
coefficients remain allowed. The scheme/field universe u and coefficient/module
universe u+1 agree with the dependency interfaces; finite rings can be realized
there, and no independent test universe makes a condition vacuous. All variables
and universes in the declaration are explicitly bound.

Independent searches: LeanFinder query "Derived pushforward along an open
immersion preserves constructible complexes over finite rings" returned eight
hits about constructible images and scheme-module restriction/pushforward, not
this theorem. Loogle `"rightDerivedLowerStar"` returned zero hits. LeanSearch
query "Constructibility and boundedness of derived pushforward of finite torsion
sheaves along open immersions" was unavailable (Internal Server Error), recorded
without a mathematical verdict. Direct rg searches in Mathlib for
`boundedConstructible|isBoundedConstructible` returned no match. Searches in
WeilConjectures and lean/Sheaf for bounded-constructible lower-star statements and
open-image finiteness found the upstream theorem in Derived.Finiteness.DirectImage.
I opened its full signature, its ambient variables, and its constructibility
dependencies: it uses DerivedCategory.boundedConstructible and
Scheme.IsConstructibleSheaf (finite generation of geometric stalks), whereas this
node's recorded dependency uses isBoundedConstructible and
IsConstructibleEtaleModuleSheaf (finite constant values on a stratification).
These require a bridge, so it is not the required existing declaration. No exact
side-project duplicate or upstream name collision was found. The statement reuses
all required notions and introduces no definitions.

H5-H9: there is one theorem with whole proof `by sorry`, no hollow construction,
private notion, local notation or local instance. The module and theorem docstrings
name the source and blueprint ID. The theorem docstring follows all six proof steps:
primary splitting and prime filtrations; prime-field comparison; inherited A-action;
long exact sequence reconstruction; the truncation spectral sequence rectangle;
stabilized constructibility and the finite abutment range. Public imports supply
the statement's vocabulary and ordinary imports retain the recorded available
proof dependencies. No line exceeds 100 characters.

No mathematical or signature mismatch was found; no Lean or node changes were
needed. This reading adds only this report section. There are no new definition
nodes, replacement dependency modules, or statement corrections to audit.

Second-reader validation: scompile.py completed cleanly: the delivered module
compiled in 1.6 s, with no errors or warnings, nice 19, two threads and the
60-second per-file limit. Its overlay prerequisites SmoothBaseChangeCoefficients
and EtaleConstantModuleDirectImageLeftExact compiled in 1.4 s and 9.3 s.
A text check confirms lean.statement equals the file signature verbatim and every
Lean line meets the 100-character limit. No local compiler or global build was run.
