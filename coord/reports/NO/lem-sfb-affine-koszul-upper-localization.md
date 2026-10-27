## Worker report

The module `Sheaf.AlgebraicGeometry.AffineKoszulUpperLocalization` states
`AlgebraicGeometry.affine_koszul_upper_localization`, with `sorry` as its entire proof.
It introduces no definitions and changes only the item's `lean` record. No statement
correction, dependency repair, new node, or mathematical dispute was needed.

Source read: `literature/stacks-project/perfect.tex`, Situation `situation-complex`
and Tag 0GEJ (`lemma-orthogonal-koszul-first-variant`), including its proof.
The latest blueprint's `sk-thm-sf-ctf-stability` unit and direct-images detail were
consulted for the inherited supporting-tool route. The node realizes only (2) implies
(1) of 0GEJ, with exactly the threshold `a`.

Hypotheses and clauses, in order:

- A commutative ring is `(A : Type u) [CommRing A]`; no nonzero-ring assumption.
- A nonnegative tuple length and its entries are `(r : ℕ) (f : Fin r → A)`.
- The affine scheme is literally `Spec (.of A)` everywhere.
- The open union is `(U : (Spec (.of A)).Opens)` together with
  `hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)`. These are the prime ideals
  not containing each `f i`. Its inclusion is `U.ι`; no arbitrary open is allowed.
- `C_f` is the explicit expression `DerivedCategory.Q.obj` of the termwise tilde
  image of `(ExteriorAlgebra.koszulComplex A r f).extend
  ComplexShape.embeddingDownNat`. The embedding sends the chain index `q` to `-q`;
  it inserts zero terms outside that image. This is the recorded Koszul complex,
  not a model specified by arbitrary isomorphism data or a new definition.
- `E : schemeDerivedQCohCategory (Spec (.of A))` supplies exactly the quasi-coherent
  cohomology condition. Its ambient derived object is `E.obj`.
- `(a : ℤ)` and `∀ n : ℤ, a ≤ n → Subsingleton (C_f⟦-n⟧ ⟶ E.obj)` express the
  original upper vanishing range. The Hom type has its zero morphism, so being
  subsingleton is precisely that its additive group is zero. No sign or endpoint
  is shifted.
- Restriction is the exact `schemeOpenRestriction (Spec (.of A)) U`: overFunctor
  followed by the canonical `Scheme.Modules.overEquiv U` into modules on `U.toScheme`.
- The map is the actual `.unit.app E.obj` of
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction` applied to
  `(Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
  (Scheme.Modules.overFunctorEquiv U).symm`. Explicit `C`, `D`, `L`, `R` arguments
  select the shared SheafOfModules category instances. Here
  `R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom`, whose right derived
  functor is definitionally `schemeDerivedDirectImage U.ι`. Thus the codomain is
  exactly `Rj_*(E|_U)`. No arbitrary map, adjunction witness, or extra hypothesis
  is substituted for the canonical unit.
- `IsIso ((DerivedCategory.TStructure.t.truncGE a).map (...))` asserts invertibility
  of that very map after the standard cohomological upper truncation, rather than
  merely existence of some isomorphism between its endpoints.
- The two `HasDerivedCategory` binders are the localization size infrastructure,
  with independent morphism universes `wY` and `wU`. They impose no equality of
  site universes, boundedness, or mathematical restriction on the two categories.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and the spectrum/open-subsheme infrastructure (available through public imports).
- `WeilConjectures.AlgebraicGeometry.KoszulComplex`:
  `ExteriorAlgebra.koszulComplex`, with its actual contraction differential.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, and its defining ringed-space direct-image functor.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`;
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`: `TStructure.truncGE`.

Additional existing infrastructure used, without redeclaration:
`WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps.schemeOpenRestriction`
(the declaration namespace is `AlgebraicGeometry`), Mathlib's
`Scheme.Modules.restrictAdjunction` and `Scheme.Modules.overFunctorEquiv`, and
`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction` from
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`.
All recorded proof-dependency modules are imported as plain imports; the proof
is reproduced in seven steps in the theorem docstring, with the node identifiers.
The direct canonical-adjunction construction avoids importing the much broader
relative-Mayer--Vietoris package, whose `mvOpenRestrictionAdjunction` uses a global
family of derived-category instances. No extra global instance family is assumed here.

Edge cases checked before writing: for `r = 0`, `Fin 0` is empty and its supremum is
bottom, while the Koszul complex is `A` in degree zero; the claim becomes vanishing
of the upper truncation on an affine scheme. For the zero ring both schemes are
empty. For all zero generators the open is empty but the Koszul test remains the
actual Koszul complex; no generator is required to be a unit or regular. If some
`f i` is a unit then `U = ⊤`, the Koszul complex is contractible and the unit is an
isomorphism. The zero object, arbitrary negative `a`, and unbounded quasi-coherent
`E` are retained. These checks give no counterexample or statement fault.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`, query "Koszul Hom vanishing on affine scheme implies
  upper truncation of open localization unit is an isomorphism": eight hits about
  ordinary affine basic-open maps and localizations, none the derived assertion.
- `msearch.py ... loogle`, query `truncGEFunctor, IsIso`: no hits (unknown identifier
  `truncGEFunctor`); source inspection located the correct API `TStructure.truncGE`.
- `msearch.py ... grep`, query `Koszul|koszul`, subdirectory `AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item identifier and
  `koszul.*[Uu]pper|[Uu]pper.*[Kk]oszul`: no hits. An exact declaration-name search
  in Mathlib, both library roots, and `dag/lean_names_upstream.json` also had no hits.
- Source searches for canonical open units located DerivedOpenRestrictionMaps and
  DerivedBaseChangeMayerVietorisMaps; their full constructions were read. Searches
  for truncGE located Mathlib's functor. No duplicate theorem was found.

Validation: `scompile.py NO lem-sfb-affine-koszul-upper-localization <module>` passed
both sandbox and actual library-path compilation (11.7 s and 20.7 s), with no errors
or warnings. The first elaboration attempts exposed a projection-parenthesization
issue and inference of the separate `Scheme.Modules` category instance. Explicitly
selecting `C`, `D`, `L`, and `R` fixed the latter without changing the mathematics or
adding an instance assumption. All universes and variables are explicitly bound.
Maximum line length is 91 characters.

## Second reading by NO

The dispatcher explicitly prohibited starting other agents; this section records the
worker's final rereading, not an independent-agent review. The maintainer's independent
review remains the review of the delivery. I reopened the node and the final signature:
A, r, f, Spec A, the finite open union, the literal sheafified Koszul object in negative
cochain degrees, quasi-coherence, a, all integers n ≥ a, the shift -n, the canonical
unit and the standard truncation at the same a each have the counterparts listed above.
The conclusion is IsIso of the canonical morphism itself. There is no arbitrary unit,
no arbitrary right adjoint, no boundedness hypothesis, and no dropped empty-tuple case.
The explicit R argument makes the derived pushforward match its recorded definition.
No mathematical mismatch was found. Only the elaboration repairs described above
were needed. The node's statement, stmt_deps, proof and proof_deps are unchanged.
