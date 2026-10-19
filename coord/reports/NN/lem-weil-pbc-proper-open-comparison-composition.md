## Worker report

The module `Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition` states the
composition and identity laws for the actual `AlgebraicGeometry.Etale.properOpenComparison`.
Both theorem proofs are `sorry`; no mathematical assertion is proved.
The helper `properOpenDirectImageCompIso` constructs the canonical derived
pushforward composition isomorphism from existing constructions, with real data.
It is not an arbitrary comparison: it is `Functor.rightDerivedFunctorPlusCompIso'`
applied to the fibre-product-pasting isomorphism `Etale.lowerStarComp`.
Its injective-preservation instance is obtained from the exact inverse-image
adjunction using `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.
This helper is part of the canonical identification explicitly mentioned by this node.
It carries the owning node's blueprint/source docstring and is listed in `lean.declarations`.

Hypothesis-by-hypothesis correspondence:

- Schemes T₁,T₂,T₃,X: `{T₁ T₂ T₃ X : Scheme.{u}}`, with explicit arbitrary universe u.
- Maps u and v: `(f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)`.
- Properness of both maps: `[IsProper f] [IsProper g]`.
  Properness of their composite is supplied by the existing Mathlib composition instance.
- The three open immersions: `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)`
  and the three `[IsOpenImmersion jᵢ]` instances.
- The commutative triangles: `(hf : j₁ ≫ f = j₂) (hg : j₂ ≫ g = j₃)`.
  The proof for the composite is explicitly constructed from associativity and these equations.
- Finite coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The commutative-ring interpretation is exactly the comparison dependency's convention.
- K in D⁺(X_et,Λ): `K : DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.

Clause-by-clause correspondence:

- `properOpenComparison_comp` equates the comparison for `f ≫ g` with
  `properOpenComparison ... g ... ≫ (rightDerivedLowerStarPlus ... g).map
  (properOpenComparison ... f ...)`, followed by the hom of
  `properOpenDirectImageCompIso` at `j₁! K`. Thus both sides have the literal
  target R(fg)_*j₁!K, and the displayed extra factor is exactly the node's
  canonical identification Rg_*Rf_* ≅ R(fg)_*.
- `properOpenComparison_id` is separately universally quantified over arbitrary
  T, X, j and K. It says that alpha for `𝟙 T`, followed by
  `lowerStarIdDerivedPlus.hom` at j!K, equals `𝟙 (j!K)`.
  It imposes no accidental composable-map hypotheses on the identity case.

Statement dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProperOpenComparison`:
  `AlgebraicGeometry.Etale.properOpenComparison` (and its specified
  `properOpenIdentification`, read in full).
- `Sheaf.AlgebraicGeometry.DerivedCategories`:
  the recorded existing `DerivedCategory.Plus` of the module-valued small-etale sheaf category;
  no alternative derived category or SheafOfModules encoding is introduced.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `lowerStarComp`, `upperStarLowerStarAdjunction`.
  The derived definition recorded alongside lowerStar is in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `rightDerivedLowerStarPlus`; this module also gives `lowerStarIdDerivedPlus`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, used with
  `Functor.mapDerivedCategoryPlus` and the exactness instances imported by the comparison module.

The module imports the stated proof-dependency modules. The proper-open-section
and proper-open-identification proof nodes have no Lean record in the snapshot;
no import is invented for them. Their needed constructions already occur in the
comparison definition; these are proof prerequisites, not missing statement objects.
The full six-step proof of the node is preserved as natural-language theorem
docstrings (steps 1–5 in the composition theorem, step 6 in the identity theorem).

Edge cases checked: X empty and ambient schemes empty are permitted; no nonemptiness,
separatedness beyond properness, finiteness of the schemes, or torsion-amplitude
hypothesis is added. K may be zero or have any lower cohomological bound, and
no specific bound or representative is chosen in the statement. The zero ring
is permitted by CommRing and Finite. Identity maps and arbitrary open immersions
are included in the identity theorem. Universes match the existing constant-module
six-functor encoding, with schemes in u and coefficients/modules in u+1.

Searches for existing declarations:

- msearch.py / leanfinder: "Proper open comparison extension by zero derived pushforward
  compatibility with composition and identity" returned eight unrelated extension
  results (SimpleFunc, bounded continuous functions, AbstractCompletion); no match.
- msearch.py / loogle: "AlgebraicGeometry.Etale.rightDerivedLowerStarPlusComp,
  AlgebraicGeometry.Etale.properOpenComparison" returned no hits; the first proposed
  name is unknown to the index.
- msearch.py / grep: "properOpenComparison|properOpen.*comp|lowerStarCompDerivedPlus"
  returned zero Mathlib hits.
- rg of WeilConjectures for the item id and `properOpenComparison|properOpen.*comp`:
  no hits. Broader derived-coherence searches found the canonical composition
  constructor in `CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusComp.lean`
  and the canonical identity constructor in `Derived/UpperLowerStarCoherence.lean`;
  these are reused. Refinement-specific comparison laws in LowerShriekCoherence
  use a different comparison and compactification data, so do not already state
  the present theorem about the specified properOpenComparison.
- rg of lean/Sheaf for properOpenComparison: only its defining module, with no laws.

Validation: the prescribed scompile.py compiled the delivered file successfully
(first elaboration and the library-path pass), with no warnings or errors.
No node correction, new node, dependency repair, or STATEMENT-DISPUTED issue was needed.


## Second reading by NN

I independently opened the item node and its six-step proof, the original blueprint
source at sec-smooth-purity/sk-def-sf-operations (order 1483), all four statement
prerequisite nodes, and the source declarations they record. I also read Stacks
sites-cohomology.tex, Tags 0730, 0D6E and 0D6G: these concern exact inverse-image
adjunctions, canonical derived composition and restriction of direct images. They
add no Noetherian, nonemptiness, constructibility or characteristic hypothesis to
this constant-coefficient comparison statement. There is no statement_change,
new node or dependency module in this delivery.

Object, hypothesis and conclusion inventory, with correspondence and verdict:

1. Arbitrary schemes T₁, T₂, T₃ and X: `{T₁ T₂ T₃ X : Scheme.{u}}`, with
   `universe u` explicitly declared. Exact match; no geometric extra instances.
2. Composable morphisms u and v: `(f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)`.
   Exact match (renamed to avoid collision with the universe variable).
3. Both morphisms proper: `[IsProper f] [IsProper g]`. Exact match. Properness
   of `f ≫ g` is inferred, rather than supplied as an extra assumption.
4. Three opens from the same X: `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
   (j₃ : X ⟶ T₃)` and `[IsOpenImmersion j₁] [IsOpenImmersion j₂]
   [IsOpenImmersion j₃]`. Exact match; no quasi-compactness of these opens.
5. The triangles commute: `(hf : j₁ ≫ f = j₂) (hg : j₂ ≫ g = j₃)`.
   Exact match. The composite triangle is the explicit associativity/congruence
   expression passed to `properOpenComparison`; it is derived from hf and hg.
6. Finite constant coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
   Exact match to the finite commutative ring specified by the comparison
   definition and the node's proof step 1; no nonzero or invertibility condition.
7. Arbitrary bounded below K: `K : DerivedCategory.Plus
   (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Exact match to the
   recorded DerivedCategories module and the comparison signature. It is the
   small-etale constant-module category, with arbitrary lower bound.
8. The actual comparison construction: both theorems use
   `AlgebraicGeometry.Etale.properOpenComparison`. I read its definition and
   `properOpenIdentification`: alpha applies j₂! to the inverse of the specified
   theta and then the derived counit; theta is the r/e/c composite prescribed
   by the prerequisite node. Exact match, with no replacement map.
9. Composition conclusion: `properOpenComparison ... (f ≫ g) ... K` equals
   alpha_g followed by `(rightDerivedLowerStarPlus ... g).map alpha_f`, followed
   by `(properOpenDirectImageCompIso Λ f g).hom.app (j₁! K)`. Both sides run
   from j₃!K to R(fg)_*j₁!K. Exact match to the displayed equation with its
   canonical identification, respecting Lean's diagrammatic composition order.
10. The canonical identification is actual data:
    `properOpenDirectImageCompIso` applies the existing
    `Functor.rightDerivedFunctorPlusCompIso'` to `Etale.lowerStarComp`. I read
    both definitions and the constructor's unit characterization: lowerStarComp
    is fibre-product pasting, and its derived version is normalized on bounded
    below injective complexes. The helper supplies injective preservation from
    the existing inverse-image adjunction, not a new theorem or an assumption.
    Its direction Rg_*Rf_* to R(fg)_* is correct. Exact match.
11. Identity conclusion: separately quantified `properOpenComparison_id` uses
    arbitrary T, X, j and K, and states `alpha_id ≫
    (lowerStarIdDerivedPlus ... T).hom.app (j! K) = 𝟙 (j! K)`.
    I read lowerStarIdDerivedPlus, which derives the underived identity
    pushforward isomorphism. Exact match; the identity case does not inherit
    unrelated f/g hypotheses or quantify only over a chosen composition.

Edge cases: empty X and empty ambient schemes are allowed whenever the stated
maps exist; the zero object and every lower bound of K are allowed. There is
no degree parameter to exclude degree zero. CommRing permits the zero ring,
Finite adds no nontriviality, and every characteristic is permitted. Schemes
have an arbitrary common size u, and the coefficient/module size u+1 is exactly
the recorded constant-module six-functor convention; finite coefficient rings
may be lifted to that size. No independent smaller test universe or new universe
equality is imposed. No indexed-family nonemptiness issue occurs here.

Independent duplicate searches (logged by msearch.py): LeanFinder query
"extension by zero proper refinement composition derived direct image identity"
returned eight unrelated function-extension declarations; Loogle query
`"properOpenComparison"` returned no hits; grep query
`properOpenComparison|properOpenDirectImageCompIso|proper_open_comparison`
returned no Mathlib hits. Direct rg over Mathlib, WeilConjectures and lean/Sheaf
found only the defining ProperOpenComparison module. Broader searches for
refinement comparisons found the theorems
`refinementOpenImmersionLowerShriekComparison_comp` and
`refinementOpenImmersionLowerShriekIso_hom_comp` in LowerShriekCoherence.
I opened their signatures and their comparison definitions: they use bundled
compactifications and their own base-change comparisons, not this node's named
properOpenComparison and specified theta. Therefore they do not already state
this item. The general composition and identity constructors are reused here.

No mathematical or signature mismatch was found; the Lean and node were retained.
The only change of this reading is this independent review section. All three
declarations have the owning source/blueprint docstrings; the composition proof
covers node steps 1–5 and the identity proof covers step 6. The two theorem proofs
are wholly sorry, and the helper has real data with no sorry. No unbound variable,
local notation, private definition, statement let or extra hypothesis was found.
The node's lean.statement was checked byte-for-byte against the main theorem
signature. Every line of the module is at most 100 characters.

Validation: scompile.py NN lem-weil-pbc-proper-open-comparison-composition compiled
the sole delivered module successfully in both sandbox and library-path passes
(3.3 s and 3.8 s), with no errors or warnings.
