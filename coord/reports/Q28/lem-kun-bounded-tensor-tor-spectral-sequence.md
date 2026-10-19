## Worker report

Item: `lem-kun-bounded-tensor-tor-spectral-sequence`.
Module: `Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence`.
Main declaration: `DerivedCategory.bounded_tensor_tor_spectral_sequence`.
The theorem is stated with `sorry`; the three display helpers contain real data.
No statement correction, new DAG node, or dependency repair is needed.

Read the node and all six statement-dependency records, their recorded declarations and
source documentation. Read Stacks More on Algebra, the section labelled
`section-kunneth-spectral-sequence`, including `proposition-kunneth-filtered` (0H7Y) and
`lemma-kunneth-spectral-sequence` (0H7Z), in the existing source cache, lines 15420–15832.
The docstring follows the node's seven proof steps, including reindexing and descent to
derived morphisms. No proof of those steps is supplied in stage 2.

Clause-by-clause rendering:

- The commutative ring is the explicit section variable `R : Type u` with `[CommRing R]`.
  `[HasDerivedCategory.{w} (ModuleCat.{u} R)]` chooses the cochain derived category with
  arbitrary Hom universe `w`; it is an infrastructure choice, not a ring condition.
- Both arguments range over `DerivedCategory.Bounded (ModuleCat.{u} R)`, the exact
  Mathlib bounded full subcategory, with inclusion `C.obj` and `D.obj`.
- Ordinary derived tensor is `C.obj ⊗ D.obj`, using the upstream K-flat derived monoidal
  structure from `HasMonoidalDerivedCategory` and the existing module flat-resolution
  instance. Its construction is the left-derived tensor of the homotopy-category total
  tensor, via K-flat representatives, and agrees with the fixed-second-factor derived
  functor in the recorded dependency. No arbitrary monoidal structure or tensor functor
  is assumed or chosen. The integral sibling already uses this same interface.
- `S` is a curried functor from the two bounded categories to
  `E₂CohomologicalSpectralSequence (ModuleCat R)`. This is Mathlib's `SpectralSequence`
  beginning at integer page 2, with shape `ComplexShape.up' (s, 1-s)` on `ℤ × ℤ`.
  Thus every page is a complex of R-modules, every successor is its homology, and the
  differential goes from `(p,q)` to `(p+s,q-s+1)` exactly as required.
- `kunnethIntegerTor R k` is `Tor' (ModuleCat R) k.toNat` for `0 ≤ k`, and the constant
  zero bifunctor for `k < 0`. In particular negative Tor is zero, rather than Tor-zero
  obtained by an unguarded integer-to-natural conversion.
- `kunnethTorPage R p q C D` is the module coproduct over the subtype
  `{ij : ℤ × ℤ // ij.1 + ij.2 = q}` of
  `Tor_{-p}(H^{ij.1}(C), H^{ij.2}(D))`. In modules this coproduct is the direct sum.
  `e₂` identifies it with the second page at every integer bidegree.
- Functoriality of the spectral sequence in both arguments is expressed by `S` itself.
  The map for `f : C ⟶ C'`, `g : D ⟶ D'` is
  `(S.map f).app D ≫ (S.obj C').map g`, a spectral-sequence morphism, hence compatible
  with page differentials and successor-page homology identifications. Functor laws and
  naturality in the functor category include identities, composition, and interchange.
- `kunnethTorPageMap` is `Sigma.map` of the actual first- and second-variable Tor maps
  on `H^i(f)` and `H^j(g)`. The second conjunction says that this direct sum is the
  induced page-two map under `e₂`, for all pairs of derived morphisms.
- For every integer `n`, `F C D n` is the recorded `DecreasingFiltration` on
  `(homologyFunctor (ModuleCat R) n).obj (C.obj ⊗ D.obj)`. Its first conjunction
  requires integer endpoints `a,b` with step `a = ⊤` and step `b = ⊥`, exactly finite
  decreasing filtration. It does not require the zeroth step to be the whole object.
- `N C D n p` with `hN` specifies a page at least 2. At every page `r ≥ N`, both
  `dFrom` and `dTo` vanish at `(p,n-p)`. Every integer bidegree is of this form by
  taking `n=p+q`. This explicitly expresses stationarity, without assuming finite
  global dimension, bounded Tor degrees, or a first-quadrant spectral sequence.
- `eInf` identifies `(F C D n).gr p` (the canonical cokernel quotient of step `p+1`
  into step `p`) with the entry `(p,n-p)` on every sufficiently late page. The fourth
  conjunction requires these identifications to commute with the canonical passage
  from cycles through homology to the successor page. Since both differentials are
  zero there, these are exactly coherent identifications with the stationary value
  `E_infinity`, not arbitrary unrelated isomorphisms of late-page objects.
- For every `f,g`, the final conjunction supplies step maps `a n p`. Their arrow
  equation identifies their underlying map with the actual
  `H^n(f.hom ⊗ₘ g.hom)`, so it preserves each filtration step.
- The same conjunction supplies graded maps `b n p` and their equation with
  `cokernel.π`, fixing them to be the induced quotient maps. Its final square identifies
  these maps with the page map under `eInf`, at every page late enough for both source
  and target. This is precisely naturality of the stationary graded identifications.
- There are no finite generation or finite global dimension hypotheses, and no assertion
  that the tensor itself lies in the bounded derived category.

Dependency declarations used:

- `def-weil-pbc-bounded-derived-subcategories`: Mathlib's
  `DerivedCategory.Bounded` and `Bounded.ι`, in
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`. Its node is a Mathlib leaf;
  its `mathlib_match` lists the Plus/Minus/Bounded definitions even though its principal
  declaration field is Plus. The source gives Bounded as `t.bounded.FullSubcategory`.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `HasDerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; cohomology is the existing
  `DerivedCategory.homologyFunctor` in `DerivedCategory.HomologySequence`.
- `lem-pc-derived-tensor-second-factor-functor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor`, in
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`. Its full declaration and
  docstring were read. The module is imported for the identification/proof plan;
  the statement uses the existing canonical upstream monoidal tensor directly.
- `def-weil-pbc-tor-modules`: `CategoryTheory.Tor'`, in
  `Mathlib.CategoryTheory.Monoidal.Tor`, left-derived in the first variable, with its
  existing `Tor'_map_app` and `Tor'_obj_map` meanings for maps.
- `def-sp-spectral-sequence`: `CategoryTheory.SpectralSequence`, its `Hom` and category,
  and `E₂CohomologicalSpectralSequence`, in
  `Mathlib.Algebra.Homology.SpectralSequence.Basic`.
- `def-sp-filtration`: `CategoryTheory.DecreasingFiltration`, fields `F` and
  `F_succ_le`, and `DecreasingFiltration.gr`, in
  `WeilConjectures.CategoryTheory.Abelian.Filtration`. The local older upstream checkout
  lacked this file; `scompile.py --source` supplied the current canonical source.
  Its specialized `IsFiniteSeparated` has a zeroth-step condition not present here;
  the theorem therefore writes the node's arbitrary finite endpoints explicitly.

Other statement imports supply the existing module projective resolutions, functorial
flat resolutions, and canonical derived monoidal instance. Proof-only imports include
`BoundedFlatKFlat`, `BoundedFilteredComplexPageCore`, the recorded second-factor theorem,
and Mathlib's derived fractions (including representation and common-refinement lemmas).
The two filtered K-flat proof prerequisites have no recorded Lean module on this base;
this theorem does not need their interfaces to type its statement, and the proof outline
retains their DAG names for stage 3. No duplicate of those independent statements is made.

Edge cases checked mathematically before writing:

- Zero ring and zero derived arguments remain allowed: the Tor sums, pages, and abutment
  may all be zero, and the finite filtration still has top and bottom endpoints.
- Complexes concentrated in any integer degree are allowed; neither bounded category nor
  filtration endpoints impose nonnegative support or a distinguished zeroth step.
- Positive `p` gives negative homological Tor degree and therefore a zero summand.
  `p=0` gives Tor-zero, not a vanished term. The formula includes all integer pairs `i,j`.
- Infinite modules and arbitrary commutative rings are allowed. For example a ring with
  nonzero Tor in arbitrarily high degrees can give an unbounded-below derived tensor;
  finite filtration length in each total degree and stationary pages do not exclude it.
- `n=0`, negative total degrees, and negative filtration indices use the same equations.
- Different bounds on source and target are handled by the common late page in the final
  equation, rather than requiring a natural choice of bounds or a global uniform page.

Searches (2026-10-16):

- `msearch.py ... leanfinder "For bounded derived complexes of modules a functorial
  spectral sequence has second page Tor of cohomology and converges to cohomology of
  derived tensor product"`: eight hits, including `Rep.torIso`, Ext connecting maps,
  Tor vanishing for projectives and group cohomology exactness; no matching theorem.
- `msearch.py ... loogle "CategoryTheory.Tor, CategoryTheory.SpectralSequence"`: zero
  hits. An earlier query containing a literal escaped apostrophe was malformed and
  returned unknown identifier `x27`; it was rerun with the valid query above.
- `msearch.py ... grep "kunneth|Kunneth|Tor.*[Ss]pectral|[Ss]pectral.*Tor"
  Algebra/Homology`: one generic spectral-sequence page-functor documentation hit;
  no Kunneth spectral sequence.
- `msearch.py ... leansearch "Kunneth spectral sequence of bounded derived tensor of
  modules"`: service unavailable, Internal Server Error; no result or verdict inferred.
- `rg` with the same Kunneth/Tor-spectral patterns in `WeilConjectures` and
  `lean/Sheaf`: geometric Kunneth statements and the integral bounded short exact sequence,
  not this general Tor spectral sequence. The integral sibling confirms the exact tensor,
  coproduct, Tor, and bounded-category conventions used here.
- `rg` for the item id in upstream `WeilConjectures`: no existing declaration.
  Searches of the proposed helper/theorem names in the upstream declaration index and
  both Lean source roots found no name collision.
- Read Mathlib spectral-sequence, derived-category/t-structure, and Tor source signatures;
  read upstream `HasMonoidalDerivedCategory` and the module flat-resolution instance.
  Existing first-quadrant `SpectralSequence.pageInfinity`/`Abutment` apply to natural
  bidegrees and prescribe first-quadrant endpoints, so they cannot express this integer
  bidegree spectral sequence. The statement uses actual stationary pages directly.

Validation: `scompile.py Q28 lem-kun-bounded-tensor-tor-spectral-sequence
lean/Sheaf/Algebra/Homology/BoundedTensorTorSpectralSequence.lean` passed with no errors
or warnings, in both the sandbox and final module-name checks (7.1 s and 42.9 s,
respectively, under the 60 s file limit). The node record contains the main signature
verbatim and lists all four declarations; the node differs from the base only in `lean`.
All Lean lines are at most 100 characters. There is exactly one postponed proof, the
named main theorem. The required delivery dry run is the final check. The independent
second reader is to write their own review section.

## Second reading by Q28

I independently read the node, the complete Lean module, all six statement-dependency
records and their actual declarations. I read the cached Stacks `more-algebra.tex`,
lines 15420–15832: the section's flat/K-flat assumptions, filtered resolution lemma,
Proposition 0H7Y, Lemma 0H7Z, and its reindexing proof. The flatness assumptions are
conditions on the chosen resolutions, not extra assumptions on the bounded inputs.
The node intentionally states the commutative-ring version with derived functoriality.

Here is my object/hypothesis/conclusion inventory and its Lean correspondence.

1. An arbitrary commutative ring R: `variable (R : Type u) [CommRing R]`.
   Verdict: exact, including the zero ring and every characteristic. There is no
   Noetherian, finite generation, or global dimension condition.
2. The cochain derived category of R-modules, in a chosen localization universe:
   `DerivedCategory (ModuleCat.{u} R)` under
   `[HasDerivedCategory.{w} (ModuleCat.{u} R)]`. I read `DerivedCategory`, `Q`,
   `HasDerivedCategory.standard` and the cohomological convention. Verdict: exact;
   w is independent of u and is the node's existing size convention.
3. Two bounded derived objects: every object binder is
   `C D : Bounded (ModuleCat.{u} R)`. I checked `Bounded` is the standard
   t-structure's bounded full subcategory, and `C.obj`, `f.hom` are its inclusion
   on objects and morphisms. Verdict: all bounded cohomology objects and all their
   derived morphisms, with no termwise model or bounded tensor assumed.
4. Ordinary K-flat derived tensor: `C.obj ⊗ D.obj`, with map `f.hom ⊗ₘ g.hom`.
   I read the recorded fixed-second-factor theorem and upstream
   `DerivedCategory.hasDerivedMonoidalCategory`, its K-flat construction and the
   module functorial-flat-resolution instance. Verdict: the existing derived total
   tensor, with the correct order of factors; no arbitrary tensor or comparison is
   postulated. The integral Kunneth sibling uses the same canonical structure.
5. A spectral sequence in R-modules, pages s >= 2, and differential
   `(p,q) -> (p+s,q-s+1)`: the value of `S` is
   `E₂CohomologicalSpectralSequence (ModuleCat.{u} R)`. I unfolded its source
   abbreviation to `SpectralSequence` with `ComplexShape.up' (s,1-s)` on
   `ℤ × ℤ`, and read the page, homology isomorphism and morphism fields.
   Verdict: exact, with no first-quadrant restriction.
6. Page two is the sum over i+j=q of Tor_{-p}: `e₂` identifies the page with
   `kunnethTorPage R p q C D`. Its coproduct index is precisely the integer-pair
   subtype with that equation. `kunnethIntegerTor R (-p)` uses the dependency's
   `Tor'` (derived in the first variable), and is the zero bifunctor in negative
   homological degrees. Verdict: exact; the index is not truncated to natural
   degrees before checking its sign. I checked the two branches and the actual
   `Tor'` definition and map signatures.
7. For every integer n a finite decreasing filtration on H^n of the tensor:
   `F C D n : DecreasingFiltration ((homologyFunctor ... n).obj (C.obj ⊗ D.obj))`,
   with the first conjunct `∃ a b, ... F a = ⊤ ∧ ... F b = ⊥`.
   Verdict: exactly the dependency node's finite filtration. The upstream
   `IsFiniteSeparated` has the extra F^0=top convention, so correctly is not used.
8. E-infinity is the stationary value and the graded piece is identified with it:
   `N`, `hN`, the third conjunct killing `dFrom` and `dTo` on every page r >= N,
   and `eInf` from `(F C D n).gr p` to the page at `(p,n-p)`.
   I checked `.gr p` is the cokernel of F^{p+1} -> F^p in the recorded filtration
   module. The fourth conjunct equates the maps from cycles through the current
   page and through homology plus the successor-page isomorphism.
   Verdict: exact stationary convergence; the late-page identifications are
   coherent with the actual spectral-sequence transition, not unrelated choices.
9. Functoriality in both arguments, including compatible page maps: the curried
   functor `S` supplies identity, composition and interchange, and its values on
   morphisms are actual `SpectralSequence.Hom`s. The second conjunct commutes with
   `e₂` and `kunnethTorPageMap`; I checked that helper is `Sigma.map` of the two
   Tor maps on the cohomology maps. Verdict: exactly the requested E₂ map.
10. The abutment map is H^n(u tensor-derived v), preserves every filtration step,
    and commutes with the graded identifications: the last conjunct supplies `a`
    with its subobject-arrow square for precisely
    `(homologyFunctor ... n).map (f.hom ⊗ₘ g.hom)`, and `b` with its cokernel
    projection square. The final equation identifies `b` with the spectral page
    map under `eInf` on every common sufficiently late page. Verdict: exact.
    Monicity of the step inclusions and epicity of the cokernel projections fix
    these induced maps, so separate existential choices do not lose functor laws.

Edge cases: zero inputs and the zero ring are allowed; complexes supported in any
integer degree, n=0, and negative total and filtration degrees are included. For p>0
the Tor degree is negative and the helper is zero; for p=0 it is genuinely Tor_0.
The sum includes every integer pair, without a finite-support hypothesis on the
inputs. If relevant summands are all zero the coproduct and filtration may be zero;
no nonemptiness condition is imposed. There is no scheme, so empty schemes do not
occur. Infinite modules and rings with arbitrarily high nonzero Tor are covered:
only the filtration in each degree is finite; the tensor may be unbounded below.
The bounds need not be uniform across different source and target objects. All
universes and variables are explicitly bound, and the independent Hom universe is
not specialized to the module-carrier universe.

Independent duplicate searches, run with `msearch.py` for this item:

- LeanFinder: `Kunneth Tor spectral sequence bounded derived tensor` returned
  tensor-existence infrastructure and Tor/Tor' declarations, not this theorem.
- Loogle: `"Tor", "SpectralSequence"` returned the three generic page-functor
  declarations; none constructs a Kunneth sequence or its natural filtration.
- LeanSearch: `Tor spectral sequence for tensor product of bounded complexes`
  returned tensorObj/HasTensor/tensorHom, Tor/Tor', and Rep.Tor_obj/Rep.torIso.
  These describe ordinary tensor or a single module resolution, not this statement.
- msearch grep: `Kunneth|kunneth|Tor.*Spectral|Spectral.*Tor` in Algebra/Homology
  returned only generic spectral-sequence documentation.
- I also searched the full Mathlib, upstream `WeilConjectures`, and project's
  `lean/Sheaf` with Kunneth, Tor/spectral, integer-Tor and negative-Tor variants.
  I opened the relevant Tor and spectral-sequence declarations and the integral
  bounded Kunneth module. No exact existing theorem, integer-Tor extension or
  displayed-page helper was found; the field/geometric Kunneth and Grothendieck
  sequence declarations are different notions. Proposed names have no collision.

No new nodes or dependency modules are in the delivery; all six interfaces supply
the stated objects. Proof-only prerequisites without recorded declarations are not
needed to type this statement. Recorded proof dependencies with modules are already
available through the imports; the seven-step proof docstring retains the two
filtered K-flat prerequisites for stage 3.

No mismatch was found, so I changed no Lean declaration, node statement or Lean
record. I added this independent review. The three definitions contain real data;
the only postponed proof is the named main theorem with its seven-step source
docstring. Every declaration has its source and blueprint marker; lines are <=100
characters and there is no file-local notation, private definition or local instance.
I checked `lean.statement` against the exact file signature: equal verbatim.
Compilation through `scompile.py` completed without errors or warnings. The delivery
dry run and final delivery below are the remaining mechanical checks.
