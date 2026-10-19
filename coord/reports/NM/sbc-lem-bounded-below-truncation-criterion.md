## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion` states
`AlgebraicGeometry.Etale.boundedBelow_truncation_criterion`, with one `sorry` and no new
constructions. The source read is the complete blueprint file
`sec-smooth-base-change/sk-rem-rest/sbc-lem-bounded-below-truncation-criterion.md`, order
1439, including its proof. Its expanded DAG statement is retained unchanged.

Hypotheses and clauses:

- All four schemes are `Scheme.{u}`. The binders `g : T ⟶ S`, `f : X ⟶ S`,
  `e : Y ⟶ T`, and `h : Y ⟶ X`, with `_sq : ChosenCartesianSquare e h g f`, express
  the specified Cartesian square. This allows the chosen fibre product rather than
  requiring definitional equality with Mathlib's chosen object: the recorded structure
  includes the chosen isomorphism with `pullback g f` and both projection equations.
- `P : Set ℕ` encodes the set of primes; the existing torsion predicate tests only prime
  members, so nonprime members have no effect and there is no extra assumption on P.
- `K : AbelianDerivedCategoryPlusTorsionOfPrimes T P` is exactly the recorded full
  subcategory of bounded-below abelian etale complexes with allowable torsion cohomology.
  `K.obj` is its underlying unbounded derived object. `n : ℤ` permits every integer.
- The first `IsIso` is the image under `DerivedCategory.homologyFunctor _ n` of the
  image under `hypercohomologyFirstFunctor g` of
  `(DerivedCategory.TStructure.t.truncLEι n).app K.obj`. Thus it is precisely the
  canonical map H^n(Rg_* τ≤n K) → H^n(Rg_* K), not an unspecified isomorphism.
- The second `IsIso` uses `hypercohomologyBaseChangeFunctor g f`, i.e. Rg_* followed
  by f⁻¹ on derived categories, applied to the same canonical inclusion.
- The third `IsIso` uses `hypercohomologySecondFunctor h e`, i.e. e⁻¹ followed by Rh_*,
  again applied to the same inclusion. It does not assume a base-change isomorphism.
- The last conjunct quantifies over every bounded-below representative `L` with
  `Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj)`. This introduces no assumption on K:
  such representatives exist for every object of D^+. For every `r : ℕ` with `2 ≤ r`
  and `q : ℤ` with `n < q`, all three `hypercohomologyCouple` pages at `(n-q,q)`
  are `IsZero`. Their total degree is n. This is exactly that only H^q(K) with q ≤ n
  can contribute, expressed with the actual recorded spectral sequences, for all
  representatives rather than depending on an arbitrary choice. Page r denotes E_r,
  as documented in the owning module. No extra lower bound or convergence claim is added.

The functors are written on the ambient unbounded derived category, as in the recorded
hypercohomology interface. Their restrictions to bounded-below objects are the node's
bounded-below derived functors; no resolution, coefficient identification, or new functor
is chosen here. Abelian sheaves use `AddCommGrpCat.{u+1}`, exactly as the recorded
allowable-torsion category, with no equality of site object and morphism universes imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` (full structure and docstring read).
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`:
  `AlgebraicGeometry.Etale.AbelianDerivedCategoryPlusTorsionOfPrimes`,
  `allowableTorsionPlusProperty`, `allowableTorsionSheafProperty` (the entire module read).
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`,
  with `DerivedCategory.isGE_iff` and `isLE_iff` (lines 28–120 read).
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` supplies the canonical
  `CategoryTheory.Triangulated.TStructure.truncLEι` (lines 1–112 read).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`. The generic coefficient category
  includes AddCommGrpCat; these are the functors used by the hypercohomology abbreviations.
  `rightDerivedLowerStarPlus` is actually in the recorded declaration's companion module
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (lines 65–83 read).
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, its ambient `mapDerivedCategory`, and
  `mapDerivedCategoryHomologyFunctorIso` (signatures and docstrings read). These general
  exact-functor interfaces apply directly to upperStar; no dependency repair is necessary.
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`:
  `hypercohomologyFirstFunctor`, `hypercohomologyBaseChangeFunctor`,
  `hypercohomologySecondFunctor`, and `CategoryTheory.hypercohomologyCouple`.
  The definitions and `hypercohomologyFiltrations_spec` were read, including the three
  spectral-sequence page-vanishing clauses. The existing node
  `def-weil-pbc-hypercohomology-filtrations` is added to stmt_deps since the final
  contribution clause explicitly uses these pages; it was already a proof dependency.
- Proof imports: `Sheaf.CategoryTheory.TruncationHypercohomology`, declaration
  `CategoryTheory.exists_truncationHypercohomology`; and
  `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`, declaration
  `AlgebraicGeometry.Etale.upperStar_abelian_exact`. The exact-functor cohomology
  comparison is available from the public ExactFunctor import. The dictionary node is
  a reading convention, with no declaration or module to import.

Edge cases checked: K = 0; P empty (the positive annihilator 1 still permits the zero
stalk); n negative; n below any lower cohomology bound (all maps compare zero sheaves);
q = n (not forced to vanish); r = 2 (included); empty schemes; identity morphisms;
arbitrary, nonproper, nonsmooth g and f. No smoothness, properness, finite-dimensionality,
or invertibility-of-primes hypothesis was introduced. The proof in the docstring follows
all four steps of the node, including why the canonical maps, rather than just abstract
isomorphic objects, are invertible.

Searches performed:

- `msearch.py leanfinder`: "Degree n cohomology of derived etale pushforward is unchanged
  by canonical truncation above n, also after inverse image" returned eight hits,
  including CochainComplex quasi-isomorphism criteria for truncation and unrelated
  sheaf-pushforward comparisons. None states the present result.
- `msearch.py loogle`: `"rightDerived", "truncLE"` returned zero hits.
- `msearch.py grep`: `truncLE.*rightDerived|rightDerived.*truncLE|truncation.*cohomology`
  in `Algebra/Homology` returned zero hits.
- `msearch.py leansearch`: "Cohomology of a derived direct image in degree n is unchanged
  by upper canonical truncation at n" was unavailable (HTTP Internal Server Error),
  not a negative search result.
- Local rg of the upstream project and `lean/Sheaf` for truncation criterion phrases
  and the exact item id found upstream `SixFunctors/Etale/SmoothBaseChange/Derived.lean`
  and `CategoryTheory/DerivedCategory/PlusDevissage.lean`. Read their relevant full
  signatures and docstrings: upstream Derived lines 130–189 give the three isomorphisms
  for **module** sheaves, with no actual spectral-sequence page assertion.
  PlusDevissage lines 130–146 give a general t-left-exact-functor criterion. Neither
  states this node's abelian-sheaf result with its spectral-sequence clause. Therefore
  an existing:true record would not give the exact statement requested.
- rg of Mathlib, upstream WeilConjectures, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `boundedBelow_truncation_criterion` found no
  declaration collision. The project hypercohomology definitions found in the source
  search are reused, not copied.

Validation: the delivered module compiled cleanly on the server, nice 19, two threads,
60 seconds per file; the compiler reported 1.8 seconds. No local compiler was run.
The installed scompile.py now attempts a local compile before its server fallback;
therefore this work calls its `run_server` entry point directly, and forces
`run_many = run_server` during deliver2.py's dry run. This preserves the instructed
server-only compilation without changing any tool. No theorem is proved, no node
statement is corrected, and no new or dependency-repair node is introduced.

## Second reading by NM

Independent second reader, 2026-10-15. Read the sandbox node and module against the
complete blueprint source at order 1439 and its containing sk-rem-rest section.
The item's source is the blueprint, not a Stacks lemma; also read Stacks derived.tex
Lemma 015J (lemma-two-ss-complex-functor) and the exact-pullback discussion in
sites-cohomology.tex Section 0735. The general truncation argument has no smoothness,
properness, qcqs, invertibility, or characteristic hypothesis. The containing section's
smooth-base-change hypotheses are not hypotheses of this general criterion.

Object, hypothesis, and conclusion checklist (all pass):

1. Schemes T, S, X and the fibre product Y: `{Y T X S : Scheme.{u}}`, with
   `g : T ⟶ S`, `f : X ⟶ S`, `e : Y ⟶ T`, `h : Y ⟶ X` and
   `_sq : ChosenCartesianSquare e h g f`. Opened ChosenCartesianSquare: it extends
   CommSq and supplies `Y ≅ pullback g f`, with both projection equations. This is
   a chosen fibre-product square, not just a commutative square or an arbitrary Y.
2. Set of primes: `P : Set ℕ`. Opened allowableTorsionSheafProperty: only prime
   members are tested, so arbitrary extraneous nonprimes do not alter the category.
3. K in the bounded-below allowable-torsion derived category:
   `K : AbelianDerivedCategoryPlusTorsionOfPrimes T P`. Opened its abbreviation and
   allowableTorsionPlusProperty: the full subcategory imposes allowable torsion on
   every cohomology sheaf, intersected with the standard t-structure's plus property.
   Its stalk predicate uses positive annihilators with every prime divisor in P.
   `K.obj` is exactly the underlying abelian-sheaf derived object, not a module-sheaf
   replacement or a complex selected by an unproved existence assertion.
4. Every integer degree: `n : ℤ`, with no sign or lower-bound assumption.
5. Canonical inclusion: `(DerivedCategory.TStructure.t.truncLEι n).app K.obj`.
   Read Mathlib's standard t-structure, its isLE_iff/isGE_iff descriptions, and the
   truncLE inclusion API. This is upper canonical truncation, not brutal truncation.
6. First conclusion: the first `IsIso` applies `hypercohomologyFirstFunctor g` and
   then `DerivedCategory.homologyFunctor _ n` to that inclusion. Opened the functor:
   it is the actual right derived functor of `lowerStar AddCommGrpCat g`, hence the
   asserted canonical H^n(Rg_* τ≤n K) → H^n(Rg_* K).
7. Pullback conclusion: the second `IsIso` uses `hypercohomologyBaseChangeFunctor g f`.
   Its definition is Rg_* followed by the exact derived upperStar along f. Therefore
   it states H^n(f⁻¹Rg_* τ≤n K) → H^n(f⁻¹Rg_* K), with the required canonical map.
8. Third conclusion: the third `IsIso` uses `hypercohomologySecondFunctor h e`.
   Opened its definition: upperStar along e followed by right derived lowerStar
   along h. It gives H^n(Rh_*e⁻¹ τ≤n K) → H^n(Rh_*e⁻¹ K). No base-change theorem is
   assumed, and the order of the functors is correct.
9. Contribution clause: the final conjunct uses all three actual hypercohomologyCouple
   constructions at `(n-q,q)`, for `n < q` and `2 ≤ r`. Read hypercohomologyE, the
   truncation-couple construction, and BigradedExactCouple.page: `.page r` means E_r,
   via pageCouple (r-2), so E₂ is included without an indexing shift. Since p=n-q<0,
   these are precisely the forbidden terms on the total-degree-n diagonal. Later
   pages inherit vanishing as subquotients. This states the node's contribution
   assertion, with neither an extra convergence claim nor a claim at q=n.
10. Representative quantification: `∀ L : CochainComplex.Plus ...`, followed by
    `Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj) → ...`, expresses the sequences
    on any bounded-below representative of K. This is not an additional hypothesis
    on K: standard bounded-below objects admit such representatives. The construction
    uses canonical truncations and is invariant under quasi-isomorphism, so the
    all-representatives form does not strengthen the mathematical assertion.

Dependency audit: opened all statement-dependency node records and the actual signatures
of their declarations. Read HypercohomologyFiltrations, ChosenCartesianSquare, and
AllowableTorsionDerivedCategories. Read lowerStar and the generic coefficient hypotheses
in UpperLowerStar.Defs; rightDerivedLowerStarPlus is in the companion
UpperLowerStarCoherence module and is the restriction of the same right derived functor.
Read mapDerivedCategoryPlus and its compatibility with the ambient mapDerivedCategory,
and mapDerivedCategoryHomologyFunctorIso. The ambient functors used here restrict to
exactly the bounded-below functors of the dependency nodes. Also checked the proof
interfaces exists_truncationHypercohomology and upperStar_abelian_exact; the dictionary
node is expressly a convention and needs no separate import. The recorded hypercohomology
node is explicitly cited in stmt_deps. There are no new definition nodes or dependency
modules in this delivery, so no H12/H13 additions need review.

Edge cases: P empty permits the zero stalk (annihilator 1), K=0 is included, and all
four schemes may be empty. Negative n, n=0, n below the lower bound, q=n, and r=2 are
covered with the expected inequalities. Identity morphisms and arbitrary nonsmooth or
nonproper morphisms are allowed. No index family requires nonemptiness. There is no
restriction on characteristic or on allowable primes being invertible. The universe u
is bound; abelian coefficients are AddCommGrpCat.{u+1}, consistently with the recorded
small-etale and torsion interfaces. No independent site universe is forced equal to u.

Independent searches: LeanFinder query "Left t-exact derived pushforward preserves
cohomology of the upper truncation in degree n" returned Ext and derived-functor
ingredients, not this statement. Loogle query `"truncLEι", "IsIso"` returned four general
t-structure truncation lemmas, none with these functors or the spectral-sequence clause.
Direct rg searched Mathlib Algebra/Homology, upstream WeilConjectures, and project
lean/Sheaf for truncation and rightDerived combinations and criterion terminology.
Read the matching upstream SmoothBaseChange/Derived.lean three isomorphism signatures:
they use ModuleCat coefficients and omit the spectral-sequence clause. Read upstream
PlusDevissage's generic left-t-exact criterion and project's
RightDerivedFunctorTruncationIso: these give ingredients, not the present combined
abelian-sheaf statement. No exact existing declaration replaces this module. The first
worker's recorded LeanSearch service failure remains an unavailable search, not a
negative result.

No mathematical mismatch was found. No Lean code or node signature was rewritten.
The module has one named theorem with sorry as its entire proof, no definitions or
new axioms, no local notation/instances, and bound variables/universes throughout.
The module and theorem docstrings identify the source and blueprint; the theorem
follows the node's four proof steps, including the essential canonical-map argument.
Checked that lean.statement is verbatim the whitespace-normalized theorem signature.

Validation: independent server compile through scompile.run_server passed; the item took
1.9 seconds, nice 19, two threads, 60-second limit, with no warnings. The tool also
compiled its unpublished dependency overlay successfully. Since the installed scompile.py
CLI tries local compilation first, this reader invokes its server entry point and sets
its in-memory run_many entry to run_server when executing deliver2.py. No tool file is
modified and no local compiler or library build is run.
