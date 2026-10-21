## Worker report

The module Sheaf.CategoryTheory.CofinalRoosRestriction states the complete node as
CategoryTheory.CofinalRoos.cofinalRoosRestriction, with sorry as its entire proof.
It supplies three owning-node helper constructions: restriction of complexes by an
order embedding, product coordinate selection, and finite-block summation. These
have real data, reuse Mathlib's whiskering, product and finite-sum constructions,
and carry the item's blueprint/source documentation. No independent notion or
new DAG node is needed. No dependency record or mathematical statement changes.

Hypotheses and objects, clause by clause:

- The site is C with Category.{vC} and GrothendieckTopology J. Module coefficients
  and values have universe max uC vC r, so every small site is admitted, including
  unequal object/morphism universes. HasSheafify and WEqualsLocallyBijective are
  the existing small-site presentation of the module category's abelian instance.
- The ring sheaf is R : Sheaf J RingCat; _hcomm asserts multiplication commutes
  on every object's sections, expressing exactly a sheaf of commutative rings.
  An arbitrary ring sheaf is allowed: no constant-coefficient restriction occurs.
- The category of modules is the recorded ringedSiteModules abbreviation,
  transparently Mathlib SheafOfModules, with no new category or abelian structure.
- HasCountableProducts expresses existence of countable products;
  HasExactLimitsOfShape (Discrete ℕ) expresses their exactness.
- X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules R) ℤ is a strict inverse sequence
  of unbounded complexes. X.asFunctor evaluates the complexes. All t_{i,j} are
  X.asFunctor.map (homOfLE h).op, so identity and composition are the functor laws,
  rather than extra assumptions on independently supplied transition maps.
- Indices n : ℕ encode the original positive index n+1. φ : ℕ ↪o ℕ encodes the
  strictly increasing positive-index function φ⁺(n+1)=φ(n)+1. On linear orders
  order embeddings are exactly strictly increasing functions; _hunbounded retains
  the explicit unboundedness condition ∀ i, ∃ n, i ≤ φ n. Such embeddings are
  automatically unbounded, so the family ρ indexed by all embeddings introduces
  no additional cases beyond the node's cofinal maps.
- restriction A φ is whiskering by φ.monotone.functor.op, applied to complexes;
  its transitions are precisely the original composite transitions.
- H(X) is the recorded roosF.obj X, namely Cone(roosU X)[-1]. roosU is 1-s.
  roosχ supplies exactly the specified shifted-cone coordinates and signs.
- selection X φ is Pi.lift of projection φ n. block X φ is Pi.lift of the sum
  over k < φ(n+1)-φ(n) of projection φ n+k followed by t_{φ(n),φ(n)+k}; this is
  exactly the finite interval [φ(n),φ(n+1)) in the node.
- The first conjunct states the telescoping square in Lean composition order:
  roosU X ≫ block X φ = selection X φ ≫ roosU X'.
- The second and third conjuncts assert QuasiIso (ρ X φ) and its actual coordinates
  biprod.map (block.f p) (selection.f (p+1)) through roosχ in every degree.
  These coordinates uniquely specify a chain map, so this is not an arbitrary
  derived-category completion, even though its existence is stated existentially.
- Naturality is roosF.map f ≫ ρ Y φ = ρ X φ ≫ roosF.map (restriction.map f),
  for every strict tower complex morphism f.
- For every increasing unbounded ψ, the composition clause identifies
  ρ X φ ≫ ρ X' ψ with ρ X (ψ.trans φ). RelEmbedding.trans applies ψ first,
  so the composite is φ ∘ ψ as required. HEq expresses only equality transport
  between the iterated and directly restricted complexes; it is equality of
  the actual cochain maps, not equality after localization or up to homotopy.
- The final conjunct is identity for the identity order embedding, again using
  HEq solely because restriction by identity has a differently presented object.
- For every P, compatible γ and hγ, roosAugment γ hγ ≫ ρ has coordinates
  biprod.lift 0 ((Pi.lift (fun n ↦ γ (φ n))).f (p+1)) for every p. This is
  exactly the restricted augmentation with zero shifted-product coordinate.
  No arbitrary augmentation is introduced. roosχ is an isomorphism, so the
  coordinate equation identifies the map itself.
- All equations concern complexes. The derived-category sentence follows by
  applying the recorded DerivedCategory.Q functor: equality and composition are
  preserved and QuasiIso maps become isomorphisms. It adds no separate structure
  or assumption to the cochain theorem.

Dependency declarations read and used:

- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  with its transparent SheafOfModules body and small-site abelian instance.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, DerivedCategory.Q and the instance inverting QuasiIso;
  the recorded strict model publicly imports this dependency already.
- Mathlib.CategoryTheory.Functor.OfSequence: Functor.ofOpSequence and
  NatTrans.ofOpSequence; their category of towers is ℕᵒᵖ ⥤ A and its ordinary
  natural transformations, exactly the tower category used here.
- Sheaf.CategoryTheory.StrictRoosModel: roosF, roosP, roosU, roosPmap,
  roosχ, roosAugment and roosAugment_χ. Read the full construction and coordinates.
- Proof dependency Mathlib.Algebra.Homology.Homotopy: Functor.mapHomotopy
  and Homotopy.homologyMap_eq (the recorded Mathlib match of
  lem-weil-pbc-homotopic-maps-equal-cohomology); imported without public.

Source read: Stacks sites-cohomology.tex, lemma-derived-limit-is-ok (0941),
and more-algebra.tex, lemma-pro-isomorphism-iso-Rlim (0H9K), including the finite
selection/block formulas, their composite formulas and the finite correction.
The theorem docstring records every one of the node's nine proof steps, including
E,J,h, the homotopy with its sign, cohomology invariance, and augmentation.

Edge cases checked before writing: identity subsequence (each block has one term),
translation φ(n)=n+c (initial unused terms are allowed), arithmetic φ(n)=e(n+1)-1
for e≥1, nonuniform quadratic φ(n)=(n+1)^2-1, zero tower, zero ring, zero P,
zero family γ, empty site, and unbounded cochain degrees. No φ(0)=0 restriction
occurs. The initial unselected block is covered by the proof's ν formula.
There is no empty tower-index case: the node fixes the nonempty positive naturals.

Searches actually run:

- msearch.py leanfinder: "A strictly increasing cofinal subsequence of an inverse
  tower induces a quasi-isomorphism of Roos mapping fibre complexes by coordinate
  selection and finite block sums, compatible with composition and augmentation".
  Eight hits: CM5b, derived-category fractions, homology-sequence and general
  quasi-isomorphism composition lemmas. None states the specified comparison.
- msearch.py loogle: "CochainComplex.mappingCone, HomotopyEquiv". Three hits:
  mappingCone.rotateHomotopyEquiv, mappingConeCompHomotopyEquiv, and
  cm5b.homotopyEquiv. These are general cone results, not subsequence comparisons.
- msearch.py grep: "Roos|roos|cofinal.*(cone|limit)|subsequence.*quasi" in
  Algebra/Homology. Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for Roos, cofinal, restriction,
  block and subsequence, plus the exact item id and proposed names. Read the
  arithmetic restriction definitions and compactSupportRoosCofinality statement.
  Those only cover arithmetic indices (the latter also constant ring sheaves),
  not arbitrary increasing subsequences of modules over any ring sheaf. The
  existing strict Roos model is reused; no matching declaration was found.

No STATEMENT-DISPUTED or node faults were found. No new nodes, dependency repairs,
or statement correction are delivered.

## Second reading by Q70

I reread the node and the complete module against the correspondence above. This
is an explicit worker self-check, not an independent-agent review: the dispatcher
forbids starting other agents, and the maintainer supplies the independent review.
I checked the first-coordinate/second-coordinate order against roosχ and
roosAugment_χ, the off-by-one positive-index encoding, the order ψ.trans φ for
φ ∘ ψ, and that neither the identity nor the initial skipped block is excluded.
The coordinate equality for the augmented composite is equivalent to equality
with the uniquely specified restricted augmentation. The initial compiler errors
were an incorrect import for HasExactLimitsOfShape and the name of the identity
embedding; these were corrected without mathematical changes.
