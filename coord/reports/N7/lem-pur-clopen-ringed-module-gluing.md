## Worker report

The module Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing states
lem-pur-clopen-ringed-module-gluing in two theorem declarations:
AlgebraicGeometry.Scheme.ProEt.clopen_ringed_module_gluing (the arbitrary ring
module equivalence and all its formulas) and clopen_integral_coefficients
(the finite and completed coefficient comparisons and their normalizations).
clopenModuleRestriction_additive states the additivity clause needed to type
ShortComplex.map; it is part of this same DAG statement, not a new lemma node.
All three theorem proofs are exactly `sorry`. Every helper definition has real
data and is an application of a published construction; G itself is existential
with its entire sectionwise characterization, never a definition chosen from an
underdetermined existence theorem.

The sources read were sites.tex, lemma-glue-sheaves (04TR), including its explicit
compatible-tuples formula; lemma-mapping-property-glue (04TS), and lemma-glue-maps
(04TQ). The empty and disjoint overlap specialization removes exactly the matching
conditions in that formula. The module docstrings give all ten proof steps,
including the ring-limit argument, with their dependency names.

Hypotheses and conclusions, matched individually:

- X : Scheme.{t}; I : Type w with [Finite I]; Y : I → Scheme.{t}; j : ∀ i,
  Y i ⟶ X. The open and closed immersion instances are precisely the clopen
  subscheme hypotheses. hdisjoint is Pairwise Disjoint of the images; hcover
  says every point of X lies in some image. There is no nonempty-index condition,
  finite-type hypothesis, or fixed field hypothesis on this arbitrary-ring part.
- The sites are exactly Scheme.ProEt with ProEt.topology. Objects have universe
  t+1 and arrows t; these are not identified. Ring coefficients have independent
  universe u; modules use max v w (t+1), allowing arbitrary coefficient and index
  sizes and enough size for sheafification. R : Sheaf (topology X) RingCat.{u},
  together with hcomm on every section ring, is a sheaf of commutative rings;
  restrictions are already ring homomorphisms. Commutativity is the only extra
  structure forgotten by using RingCat rather than CommRingCat.
- R_i is `(clopenRingRestriction (j i)).obj R`: actual precomposition by the
  weakly etale composition functor MorphismProperty.Over.map. The component
  restriction r_i is clopenModuleRestriction (j i) R, a transparent abbreviation
  for SheafOfModules.pushforward (𝟙 _). Its underlying sections, restrictions,
  actions and morphisms are precisely Mathlib's. r is their Functor.pi'.
- G, eta and epsilon give the equivalence in its explicit quasi-inverse form.
  Both triangle identities are stated. Additivity is stated as preservation of
  sums of morphisms, with pointwise sums in the product, because Mathlib has no
  product-category Preadditive instance. `Nonempty (Abelian (∀ i, ...))` states
  the product's abelian structure without inventing an instance. Both functors
  preserve finite limits and finite colimits: exactly categorical exactness.
- sigma F U is an additive equivalence with the tuple of F_i(U ×_X Y_i)
  sections. clopenTestPiece is the existing MorphismProperty.Over.pullback, not
  a new fibre product notion. Its five equations specify respectively the
  restricted R(U)-scalar action, componentwise restrictions, componentwise
  functor action on morphisms, eta as restriction to the component cover, and
  epsilon as diagonal projection. clopenDiagonal is the actual unit of
  Over.mapPullbackAdj: it identifies W with W ×_X Y_i. Thus the final formula
  evaluates the i-th projection along that canonical identification.
- e_i and the insertion functors s_i satisfy e_i = s_i ⋙ G. The diagonal
  evaluation of s_i is naturally the identity and all other coordinates are
  zero. The stated r_i e_i natural isomorphism and off-diagonal IsZero express
  the two component-extension claims. A Bicone of the functors r_i ⋙ e_i,
  with vertex the identity and IsBilimit, is precisely their natural finite
  direct-sum decomposition. This avoids any file-local biproduct instance.
- For every proposed KernelFork or CokernelCofork, universality is equivalent
  to universality after every r_i. For every ShortComplex S, S.Exact iff all
  S.map r_i are exact. These detect kernels, cokernels and exact sequences as
  categorical assertions, without asserting sectionwise surjectivity.
- For each empty Y_i its module category is equivalent to Discrete PUnit;
  an empty I forces IsEmpty X and the same equivalence for Mod(R). There is
  no false equality of object types: all module sheaves are uniquely isomorphic
  to zero, rather than being definitionally the same object.
- The coefficient theorem repeats the geometric hypotheses and introduces l
  with [Fact l.Prime], hl : IsUnit (l : Γ(X, ⊤)), E : Type u with Field,
  Algebra ℚ_[l] E and FiniteDimensional. This is exactly a prime invertible on
  X and a finite extension. Its n : ℕ encodes the node's positive exponent n+1,
  using the recorded completed-coefficient convention, including exponent one.
- `finite i n` compares restriction of integralCoefficientSheaf on X to the
  one on Y_i. `completed i` does the same for the actual inverse-limit sheaf
  completedIntegralCoefficientSheafUnrestricted. The equations preserve the
  finite constant sections (the actual commutative-ring sheafification units),
  every transition n ≤ m, each limit.π, and integral constant sections through
  integralConstantToCompletionOfUniverses. Compatibility for all transitions
  includes identities, adjacent reductions and their composites. Completion is
  never replaced by the discrete constant integral sheaf.

Dependency declarations used and read:

- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom, including their
  locally ringed space data; Mathlib.AlgebraicGeometry.OpenImmersion:
  IsOpenImmersion; Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  IsClosedImmersion (closed embedding and surjectivity on stalks).
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, ProEt.topology and
  etalePrecoverage_le_proetalePrecoverage. The exact concrete sites are used.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  a transparent abbreviation for SheafOfModules, with the Mathlib sectionwise
  linear morphisms and inherited abelian structure.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses:
  WeilConjectures.integralConstantToCompletionOfUniverses and its quotient
  cone, with independent site and coefficient universes. Its transitive owning
  module CompletedIntegralCoefficients supplies integralCoefficientSheaf,
  integralCoefficientSheafSystem and completedIntegralCoefficientSheafUnrestricted.
- Mathlib's continuous sheaf pushforward and SheafOfModules.pushforward;
  MorphismProperty.Over.pullback and Over.mapPullbackAdj provide the precise
  canonical maps used in the statement. The RingCat-facing abbreviations are
  direct specializations of these existing definitions, not a second category
  of modules or a new independent construction.
- Proof imports: Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
  (weaklyEtale_localization), Sheaf.CategoryTheory.SiteModuleSheafGluing
  (exists_moduleSheaf_of_cover), Mathlib.CategoryTheory.Adjunction.Limits
  (isEquivalencePreservesLimits and isEquivalence_preservesColimits), plus the
  recorded constant sheafification and generic limit modules. All recorded
  proof dependencies that have modules are imported, directly or transitively.

Edge cases checked: I empty; X empty with nonempty I; an individual empty
component; a singleton partition; the zero ring and zero module; unequal site
object/arrow universes; coefficient universe unrelated to t; positive exponent
one; identity transition and arbitrary n ≤ m. The second triangle identity was
checked for its composable direction. No statement correction or disputed claim.

Searches run (the sandbox searches.jsonl records the msearch calls):

- LeanFinder: `restriction finite clopen partition exact equivalence proetale
  sheaves modules product` returned eight results about TopCat ring sheaves,
  profinite partitions and unrelated exactness; none states this theorem.
- Loogle: `SheafOfModules.overFunctor, Equivalence` returned zero hits.
- Mathlib grep via msearch: `clopen|isProductOfDisjoint` in
  Algebra/Category/ModuleCat returned zero hits.
- rg in both lean/WeilConjectures and lean/Sheaf for clopen/Clopen and this
  node id, followed by exact proposed declaration-name searches. No declaration
  has this node's full arbitrary-ring statement. The existing
  PurityFiniteSetting.finiteClopen_module_equivalence was read: it restricts to
  the chosen finite/completed coefficient family over a fixed finite setting,
  finite-type base schemes, one coefficient/site universe, and does not supply
  this arbitrary-ring interface. Its restriction helpers are CommRingCat-valued
  specializations of the same Mathlib pushforward. Importing that downstream
  decomposition to restate its prerequisite would create a dependency cycle.
  This delivery directly uses the underlying recorded Mathlib constructions,
  and neither copies its coefficient-setting definitions nor adds assumptions.
- Exact searches for all proposed names in Mathlib, WeilConjectures and Sheaf
  found no existing declarations in AlgebraicGeometry.Scheme.ProEt.

Validation: scompile.py checks this individual module under its sandbox and real
module names against the live published library. No local or global build was run.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
