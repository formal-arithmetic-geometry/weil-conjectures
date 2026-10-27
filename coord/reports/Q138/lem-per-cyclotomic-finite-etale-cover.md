## Worker report

Stage 2, Q138, 2026-10-24. The inherited BLOCKED message referred to Q17's already
merged stage-1 split. The current item has status split, no lean record, and a
stage-2 queue entry. This delivery preserves the entire accepted node and adds
only its lean record. It supplies
`Sheaf.AlgebraicGeometry.CyclotomicFiniteEtaleCover`, whose main declaration is
`AlgebraicGeometry.cyclotomic_finite_etale_cover`.

The four auxiliary abbreviations are specializations of existing constructions,
not new independent notions: `cyclotomicCoverBase N` is
`Localization.Away (N : ULift ℤ)`; `cyclotomicCoverRing N` is
`AdjoinRoot (Polynomial.cyclotomic N (cyclotomicCoverBase N))`;
`cyclotomicCoverRoot N` is `AdjoinRoot.root` of that polynomial; and
`cyclotomicCoverMap N` is `Spec.map` of the quotient's coefficient algebra map.
All have real data. `AdjoinRoot` is definitionally the polynomial quotient by
`Ideal.span {f}`, as read in Mathlib/RingTheory/AdjoinRoot.lean:60-64. The ULift
only places the same integer ring in the universe of W; it imposes no relation
between the scheme universe u, the group universe v, and the field universe w
in the algebraic root assertion. All universes and variables are explicit.

Hypotheses and conclusions, in the exact order of the node:

- The positive integer order is `N : ℕ` with `hN : 1 ≤ N`. A positive integer
  is equivalently a positive natural number. The specified cyclotomic polynomial
  is Mathlib's `Polynomial.cyclotomic`; its monicity, integer coefficient image,
  and product factorization are the standard Mathlib declarations, not an
  independently supplied polynomial or extra hypothesis.
- The coefficient ring and C_N are precisely the localization and quotient
  abbreviations above. The morphism in the first display is
  `cyclotomicCoverMap N`.
- The first three conjuncts are `IsFinite`, `Etale`, and `Surjective` of this map.
  These use scheme morphism properties, including surjectivity on scheme points.
- The fourth conjunct is `cyclotomicCoverRoot N ^ N = 1`.
- The fifth is `∀ a : ℕ, 1 ≤ a → a < N → IsUnit (1 - ... ^ a)`.
  It does not restrict a to exponents coprime to N.
- The sixth quantifies over every `Ω : Type w`, `[Field Ω]`, `[IsAlgClosed Ω]`,
  and ring homomorphism `φ : cyclotomicCoverRing N →+* Ω`, and asserts
  `IsPrimitiveRoot (φ (cyclotomicCoverRoot N)) N`. A ring homomorphism is exactly
  a geometric point of the affine cover. Restriction to the coefficient ring
  supplies its geometric point on the base; equivalently this is an Ω-point
  of that geometric fibre. Conversely every geometric-fibre Ω-point gives such
  a map by projection. Thus this states the clause about every algebraically
  closed geometric fibre without choosing a noncanonical residue embedding.
  `IsPrimitiveRoot` has fields pow_eq_one and dvd_of_pow_eq_one, exactly
  multiplicative order N for N positive.
- The final conjunct quantifies over every `W : Scheme.{u}` with
  `IsUnit (N : Scheme.Γ.obj (op W))`. This is invertibility of the integer N on W:
  a unit global section restricts to units everywhere, and local inverses of N
  glue uniquely to a global inverse. It introduces the structural map
  `s : W ⟶ Spec (.of (cyclotomicCoverBase N))` by existence, then asserts
  `IsFinite`, `Etale`, and `Surjective` of
  `pullback.fst s (cyclotomicCoverMap N)`. There is no Noetherian, reducedness,
  connectedness, finite-type, nonemptiness, or characteristic restriction on W.
  The structural map s is unique by the localization universal property and the
  Gamma-Spec adjunction (node proof step 6). Hence the existential does not choose
  a different base morphism or weaken the assertion about the specified product.
- An arbitrary group action is `ρ : G →* Aut W`, for arbitrary `G : Type v`
  with `[Group G]`. The final clause asserts existence of a unique action
  `σ : G →* Aut (pullback s (cyclotomicCoverMap N))` characterized by
  `(σ g).hom ≫ fst = fst ≫ (ρ g).hom` and `(σ g).hom ≫ snd = snd` for every g.
  These are exactly the two equations defining `(w,c) ↦ (gw,c)`. They determine
  the induced action uniquely by pullback.hom_ext, so no arbitrary comparison
  map, existential uncharacterized action, or Nonempty choice replaces it.
- For every `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and geometric point
  `y : Spec (.of Ω) ⟶ pullback s ...`, the final displayed equality is
  `{g : G | y ≫ (σ g).hom = y} =
   {g : G | (y ≫ fst) ≫ (ρ g).hom = y ≫ fst}`.
  It is equality of geometric inertia subgroups of the same group, expressed
  through their underlying subsets; the induced inertia homomorphism is the
  identity on this subset. All geometric-point binders use the usual scheme
  universe convention of def-weil-geometric-point. The additional unique-action
  characterization spells out the induced product action already in the node.

Dependencies, whose node statements, recorded interfaces, and source declarations
were read:

- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  `AlgebraicGeometry.IsFinite`. The item asks for finiteness, not integrality
  as an additional conclusion.
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale`.
- def-weil-geometric-point: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`,
  with inline morphisms `Spec Ω ⟶ X`; the alternative point/residue-embedding
  equivalence `Scheme.SpecToEquivOfField` was read in
  Mathlib.AlgebraicGeometry.ResidueField.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst`, `pullback.snd`, and its universal property.
- def-weil-polynomial-ring: Mathlib.Algebra.Polynomial.Basic, `Polynomial`.
- def-weil-ring-localization-away: Mathlib.GroupTheory.MonoidLocalization.Away,
  `Localization.Away`, with its ring and algebra instances supplied by
  Mathlib.RingTheory.Localization.Away.Basic.
- def-weil-pbc-algebra-hom-quotient: its Mathlib match is `Algebra`, `AlgHom`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`; AdjoinRoot uses exactly that
  quotient algebra structure and quotient map. No dependency repair is needed.

Every stated proof dependency is available from the imports, using plain imports
for modules needed only for the proof: the cyclotomic Basic and Roots files,
AdjoinRoot (powerBasis'), StandardEtale, localization at primes, AlgebraicClosure,
Spectrum.Prime.Topology, GammaSpecAdjunction, Finite, Proper, Etale, and
PullbackCarrier. The main theorem's docstring records all seven proof steps and
names the corresponding DAG inputs. Its proof is only `sorry`; nothing is proved
at stage 2. No hollow definition or auxiliary postponed theorem is introduced.

Source verification: read ILO PDF page 130, printed p.124, VIII 5.3.6 and Lemma
5.3.7; this is exactly the trivial-action cyclotomic base change. Also read the
current blueprint's lem-per-artin-gabber-affine-curve.proof.md and Q17's reviewed
split, which supplies the expanded elementary algebraic assertions of this node.

Edge cases checked before writing: N=1 has Φ_1=T-1, C_1=ℤ and ζ=1; the difference
unit range is empty and primitivity is order one. N=2 has ζ=-1 and 1-ζ=2,
invertible on the chosen base. For composite N (e.g. N=6), all 1≤a<N are still
covered. Fields whose characteristic divides N receive no map from the base,
so none is incorrectly claimed to contain a primitive Nth root. The empty scheme
has the zero ring of global sections, in which N is a unit, and its base change
is empty; surjectivity and the geometric-point clause have their correct empty
interpretation. Arbitrary nonreduced and disconnected W remain allowed. The
acting group need not be finite or faithful; trivial actions have full stabilizer
on both sides. The case u=0 and arbitrary larger u are both covered by ULift ℤ.

Searches for an existing statement, using the prescribed msearch.py wrapper:

- leanfinder: "Primitive roots of unity over Z with N inverted give a finite
  etale surjective scheme cover with inertia preservation" returned 8 hits,
  including IsPrimitiveRoot.embeddingsEquivPrimitiveRoots and cyclotomicCharacter
  results. None states this cover, its unit differences and inertia assertion.
- loogle: `Polynomial.cyclotomic, AlgebraicGeometry.Etale` returned 0 hits.
- grep: `[Cc]yclotomic.*[Ee]tale|[Ee]tale.*[Cc]yclotomic` returned 0 hits.
- leansearch: "The cyclotomic polynomial quotient after inverting N is finite
  etale and surjective" returned 8 hits including Polynomial.cyclotomic and
  CyclotomicField, but no scheme-cover statement.
- rg over lean/WeilConjectures and lean/Sheaf for cyclotomic/Cyclotomic found the
  existing cyclotomic character, Tate module and roots-of-unity sheaf modules,
  which state different results. Read Sites/RootsOfUnity.lean to check this.
- rg for the item id in lean/WeilConjectures, and for all five new declaration
  names across Mathlib, WeilConjectures and Sheaf, found no matching declaration.

No statement correction, disputed statement, new node, or dependency module.
Compilation through scompile.py succeeded for both the sandbox and library module
with no errors or unexpected warnings. No direct git command or upstream edit was
performed.

## Second reading by Q138

I reread the accepted node and completed module clause by clause after the first
compile. This is a second pass by the same worker; the independent reading belongs
to the maintainer's delivery review, as specified in this dispatcher's brief.
The review checked especially that ζ is the actual quotient generator, that all
exponents 1≤a<N are included, that W and G have no extra assumptions, that the
second projection is fixed by σ, and that inertia uses equality of geometric
morphisms rather than only equality of underlying topological points. The ULift
was checked to be a copy of ℤ rather than a restriction to small W. The first
compiler run exposed an ambiguous `.ofHom` elaboration; it was replaced by
`CommRingCat.ofHom`, and the final module compiled cleanly. No mathematical
hypothesis or clause changed during this second pass.
