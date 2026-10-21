## Worker report

Delivered module: `Sheaf.Paper.ExactScalarPeriodicResolution`.
Primary statement: `SheafOfModules.exact_scalar_periodic_resolution`.
The accompanying `ModuleCat.scalar_periodic_free_resolution` states the ordinary-ring
clause. Definitions contain actual component data, and every theorem proof is `sorry`.
The item statement and dependencies are unchanged. No statement dispute or node fault.

Hypotheses and constructions, matched clause by clause:

- A small site is represented by `C : Type u`, `Category.{v} C`,
  `J : GrothendieckTopology C`, and `EssentiallySmall.{r} C`. Object, morphism, and
  coefficient universes are independent. The last binder expresses smallness relative
  to the module universe and supplies the existing sheafification/abelian instances.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{r}`. Its underlying ring
  sheaf is `(sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R`.
  Its module category is the recorded transparent `ringedSiteModules.{r,r,v,u}`,
  definitionally Mathlib's `SheafOfModules.{r}`. No category is reconstructed.
- The copy of O as an O-module is Mathlib's `SheafOfModules.unit`. A global scalar
  is `t : (unit ...).sections`; the existing sections type includes compatibility
  with every restriction. `ht` says the square of its value is zero for every
  `U : Cᵒᵖ`. The explicit `@id` only exposes the section ring to elaboration.
- `exactScalarMultiplication R t` is `(unitHomEquiv _).symm t`. By the source of
  `unitHomEquiv` this sends a section a to a times t, equivalently t times a in this
  commutative ring. `exactScalarMultiplication_sq` is the named square-zero theorem
  needed by the construction; it is a clause of the node's complex construction.
- `hexact` is literally equality of `kernelSubobject` and `imageSubobject` of that
  same map. It is categorical exactness of module sheaves, not sectionwise exactness.
- E and pi are `cokernel (exactScalarMultiplication R t)` and `cokernel.π`.
- `scalarPeriodicX M i` is M if `i ≤ 0`, and the zero object otherwise.
  `scalarPeriodicD f i` is f transported by those object equalities if `i < 0`,
  and zero otherwise. `scalarPeriodic` uses the actual `CochainComplex.of`
  constructor; all off-shape differentials are zero. Its named square-zero theorem
  supplies only proof data. `exactScalarPeriodicComplex` specializes this construction
  to the given scalar, without choosing an object from an existence theorem.
- `scalarPeriodicXIso` is the equality-induced identification of every nonpositive
  term. `scalarPeriodicAugmentation` uses `HomologicalComplex.mkHomToSingle` and
  exactly the degree-zero quotient map. That constructor gives zero components
  elsewhere. The named augmentation-condition theorem postpones the chain-map proof,
  not its data. `exactScalarPeriodicAugmentation` specializes this actual map.

Conclusions, in order:

1. The first `ShortComplex.Exact` conjunct is exactness of O --mu--> O --mu--> O,
   hence exactness at every repeated negative term of the augmented sequence.
2. The second is exactness of O --mu--> O --pi--> E. `Epi pi` gives exactness at E
   before the terminal zero. These three conjuncts are the entire augmented exactness.
3. `Nonempty (P.homology 0 ≅ E)` is H^0(P) isomorphic to E.
4. `∀ i : ℤ, i ≠ 0 → IsZero (P.homology i)` is precisely the other-degree vanishing.
5. `∀ i, IsFlatOnSite ... (P.X i)` is flatness of every term, using the dependency's
   existing sheafified-tensor exactness predicate, with all universes explicit.
6. `IsKFlatResolutionIndependentCoefficients epsilon` is the recorded definition:
   the actual augmentation is a quasi-isomorphism and its domain is K-flat.
7. The ordinary-ring theorem uses `S : Type r`, `[CommRing S]`, the same square-zero
   and annihilator/image equality (`t*a=0 ↔ a ∈ Ideal.span {t}`). It asserts that the
   very same componentwise complex and cokernel augmentation are a quasi-isomorphism,
   identifies its cokernel with `S ⧸ Ideal.span {t}`, and requires that this isomorphism
   carry pi(a) to the ordinary quotient of a. In every `i ≤ 0` it supplies a singleton
   `Module.Basis PUnit S (P.X i)` whose vector maps to 1 under the prescribed term
   identification. This records the augmented free resolution with the specified
   basis, including the zero ring. Its positive terms and differential formulas are
   the same actual construction as for the ringed-site theorem.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules`, `unit`, `sections`, and `unitHomEquiv`, including the
  full definition of the inverse map of the latter in `PresheafOfModules`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` and
  `CochainComplex.of`; the cochain-complex dependency's recorded specialization.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, with independent site/coefficient/module universes.
  Confirmed by `scompile.py --source` against current server source as well.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`, and the existing
  coefficient-universe sheafification instances in its public imports.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: recorded derived-category
  dependency; its public complex/homology interface supplies
  `HomologicalComplex.homology`. The statement needs cohomology of complexes and
  does not introduce a chosen derived category or an extra localization assumption.
- Proof imports: `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (`CochainComplex.isKFlat_of_boundedAbove_flat`) and the tensor dependency's
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. The former is the
  recorded generic K-flatness proof tool; its older displayed specialized interface
  can be generalized during stage 3 if needed, without changing this statement.
- Further existing constructors: `HomologicalComplex.mkHomToSingle`,
  `kernelSubobject`, `imageSubobject`, `cokernel`, `cokernel.π`, `ShortComplex.Exact`,
  `QuasiIso`, `Module.Basis`, `LinearMap.mul`, and `Ideal.Quotient.mk`.

Source and edge-case reading:

Read the current blueprint proof, especially "The examples" (Z/ell^2), and local
Stacks `sites-modules.tex` definition-flat, `sites-cohomology.tex` definition-K-flat
and lemma-bounded-flat-K-flat. The latter is Tag 06YQ, as the item's proof says.
The construction handles the transition -1 -> 0 -> 1: mu then zero. Its positive
terms are zero, and H^0 is the cokernel, not the kernel. With t=0 the kernel/image
hypothesis forces O to be zero, so the conclusion still holds; the zero ring and
empty site cause no nonemptiness or nonzero assumptions. Z/4 with t=2 and the dual
numbers with t=epsilon are the standard valid cases. Z/8 with t=4 has square zero
but kernel larger than image, showing why `hexact` cannot be dropped. Every theorem
and universe binder is explicit (`autoImplicit false`); no extra characteristic,
enough-points, terminal-object, or sectionwise-surjectivity assumption is present.

Searches performed:

- `msearch.py ... leanfinder`, query "On a ringed site a square zero scalar with image
  equal to kernel gives a periodic K-flat resolution of its cokernel": eight hits,
  including generic left/projective/injective resolutions and IsKProjective; none
  states this ringed-site theorem.
- `msearch.py ... leansearch`, query "A square zero scalar with image equal to kernel
  defines an augmented periodic free resolution of its cokernel": eight hits,
  including ProjectiveResolution.exact₀/cokernelCofork and short-complex cokernel
  homology data; none is this statement.
- `msearch.py ... loogle`, initial query "CochainComplex.of, HomologicalComplex.embed,
  SheafOfModules.unit" returned unknown identifier HomologicalComplex.embed. Retried
  successfully with `HomologicalComplex.alternatingConst`: twelve hits, the natural
  number alternating complex and its component/homology formulas. It is an ingredient,
  not the specified augmented ringed-site K-flat resolution.
- `msearch.py ... grep`, query `periodic.*resolution|alternatingConst|squareZero`
  under Algebra/Homology: alternatingConst declarations only (five displayed hits).
- `rg` over live `lean/WeilConjectures` and `lean/Sheaf`, using periodic/Periodic,
  squareZero/square_zero, and scalar-complex patterns: no general-site match.
  `Sheaf.Paper.SquareZeroPeriodicTensor` contains the parent theorem for ordinary
  rings and constant sheaves on schemes, with additional Tor computations; it is
  not this general-site statement. The exact node-id search in WeilConjectures
  returned no hit. The new fully qualified declaration-name search in Mathlib,
  WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` returned no collision.

No new nodes or dependency replacements are needed. All construction helpers are
parts of this node's prescribed complex, quotient augmentation, and one-point
clause and are listed in `lean.declarations`, each with this node's source tag and
proof docstring where applicable. All definitions have actual data.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
