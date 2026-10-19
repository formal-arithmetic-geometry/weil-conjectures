## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents` states
`AlgebraicGeometry.normalization_projective_components`. Its sole theorem has proof `sorry`.
No definition, extra node, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the projective k-scheme is `{C : Scheme.{u}}`,
  with specified structure morphism `p : C ⟶ Spec (.of k)` and `[IsHProjective p]`.
  This uses exactly def-kun-projective's finite projective-space embedding convention.
- The reduced irreducible components are presented by `Z : I → Scheme.{u}`,
  `[∀ i, IsIntegral (Z i)]`, and closed immersions `a i : Z i ⟶ C`.
  `hcomponents` says their images are irreducible components, and `hindex` bijectively
  enumerates all components, without repetitions. This is presentation data for the
  components in the node, not an additional mathematical condition on C. In particular,
  integral schemes are reduced; a reduced closed subscheme with given image is unique
  by `Scheme.IdealSheafData.reduced_induced_closed_subscheme`. Conversely every reduced
  irreducible component is integral, so this presentation excludes none of the node's cases.
- The node's N is `N : Scheme.{u}`, with coprojections
  `ι i : (Z i).normalization ⟶ N`. The hypothesis
  `hN : IsColimit (Cofan.mk N ι)` is precisely the coproduct universal property.
  It permits any choice of coproduct and does not presuppose a finite index set.
  The map is `ν : N ⟶ C`, with `hν` identifying its restriction to each summand with
  `(Z i).fromNormalization ≫ a i`. Thus N is exactly the stipulated componentwise
  normalization, built from the existing absolute integral-scheme normalization.
- `Finite I` is the finiteness of the component set; `IsFinite ν ∧ Surjective ν`
  renders finite and surjective.
- `IsHProjective (ν ≫ p) ∧ IsProper (ν ≫ p)` gives projectivity and properness of N
  over the same k.
- For every i the conclusion contains `Nonempty (Z i).normalization`,
  `∀ x, IsDomain ((Z i).normalization.presheaf.stalk x) ∧
  IsIntegrallyClosed ((Z i).normalization.presheaf.stalk x)`, and
  `IsIntegral (Z i).normalization`. These are exactly nonemptiness, normality in the
  node's explicit local-ring meaning, and integrality.
- `IsOpenImmersion (ι i) ∧ IsClosed (Set.range (ι i))` identifies the summand as
  an open and closed subscheme of N. The coproduct decomposition itself is `hN`.
- `IsHProjective ((Z i).fromNormalization ≫ a i ≫ p)` and `IsProper` of the same map
  assert projectivity and properness of each summand over k. By hν this is the structure
  morphism induced from N, not an independently chosen map.
- `topologicalKrullDim C ≤ 1 → ∀ i, topologicalKrullDim (Z i).normalization ≤ 1`
  is the exact conditional dimension assertion.
- The existential `b i : Z i ⟶ C.nilradical.subscheme` and `νred : N ⟶
  C.nilradical.subscheme` has three diagram equations. The first makes b i the
  component inclusion into the reduction, the second factors ν through reduction,
  and the third identifies νred on each summand with the very same normalization map
  followed by b i. Since reduction preserves the topological space, its components are
  these same reduced integral closed subschemes. Together with hN this is precisely
  the normalization of the reduction in the node's stipulated componentwise sense,
  not merely an arbitrary map through the reduction. No new normalization predicate
  or construction is introduced.
- `IsEmpty I ↔ IsEmpty C` is the final clause.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs), `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (Mathlib.AlgebraicGeometry.Scheme).
- `AlgebraicGeometry.IsHProjective`
  (Sheaf.AlgebraicGeometry.Morphisms.Projective), the exact def-kun-projective record.
- `AlgebraicGeometry.Scheme.normalization` and `Scheme.fromNormalization`
  (WeilConjectures.Mathlib.AlgebraicGeometry.Normalization): read the full definitions
  and docstrings; they normalize an integral scheme in its function field and do not
  assume finiteness. The local source has these at lines 179 and 185.
- `irreducibleComponents` and `IsIrreducible` (Mathlib.Topology.Irreducible),
  `AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties),
  `AlgebraicGeometry.IsOpenImmersion` (Mathlib.AlgebraicGeometry.OpenImmersion),
  `IsIntegrallyClosed` (Mathlib.RingTheory.IntegralClosure.IntegrallyClosed).
  Normal-domain stalks use the dependency's prescribed inline conjunction with IsDomain.
- `Scheme.nilradical` (Mathlib.AlgebraicGeometry.IdealSheaf.Basic),
  `Scheme.IdealSheafData.subscheme` and `subschemeι`
  (Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme) give the exact recorded reduction.
- `Scheme.IdealSheafData.reduced_induced_closed_subscheme`
  (Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme) justifies the chosen presentation
  of reduced components; read its complete statement and docstring.
- The coproduct dependency is a Mathlib leaf: read the instances for discrete colimits,
  `sigmaOpenCover`, and `disjoint_opensRange_sigmaι` in Mathlib.AlgebraicGeometry.Limits.
  Its universal property is expressed directly by `IsColimit (Cofan.mk N ι)`.
- `AlgebraicGeometry.IsFinite` (Mathlib.AlgebraicGeometry.Morphisms.Finite),
  `AlgebraicGeometry.Surjective` (Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap),
  and `AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper) render
  the convention node, which defines no new notion and has no module to import.
- `topologicalKrullDim` (Mathlib.Topology.KrullDimension) uses WithBot ℕ∞,
  so the empty scheme's dimension is allowed.
- Stated proof dependency modules are imported, including
  Sheaf.Paper.ReducedSourceFactors, Mathlib.AlgebraicGeometry.Noetherian, and
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace. Other proof-dependency declarations
  from the existing normalization module are available through its public import.
  The natural-language proof in the docstring follows all nine steps of the node.

Edge cases: I may be empty; there is no Nonempty I or IsIntegral C hypothesis.
For empty C, the family has no components and N is an empty coproduct; all per-summand
assertions are vacuous and the factorization is the unique empty-source map. Nonreduced C
is allowed and is handled by the explicit reduction. Disconnected C and components of
mixed dimensions are allowed. No perfectness, algebraic closedness, characteristic,
smoothness, or dimension hypothesis is imposed; the bound by one is conditional.
The index and scheme universes coincide, encompassing the set of components of C.

Searches for an existing statement (all performed before writing):

- msearch.py leanfinder: “Normalization of a projective scheme over a field is finite
  surjective projective and a finite disjoint union of normal integral components”.
  Eight hits, all relative normalization definitions/properties; none states this theorem.
- msearch.py loogle: `AlgebraicGeometry.Scheme.normalization,
  AlgebraicGeometry.IsHProjective`. Zero hits; unknown identifier for the project's
  absolute normalization in the Mathlib-only index.
- msearch.py grep: `normalization|fromNormalization`, AlgebraicGeometry. Ten displayed
  hits on relative normalization and Zariski's main theorem, none is this statement.
- rg over WeilConjectures and lean/Sheaf: `component.*normali|normali.*component|
  normalization_projective`; no matching theorem or componentwise normalization notion.
  rg for the node id in WeilConjectures returned no matches. The wider DAG search finds
  the current node and its users, not a separate definition to reuse. The declaration
  name `normalization_projective_components` is new.

Source checked directly in literature/stacks-project/varieties.tex: section-normalization,
lemma-normalization-locally-algebraic (0BXR), and lemma-normalize-projective (0GK4).
Their normalization decomposes into normal integral schemes, factors through the reduction,
is finite, and preserves projectivity and properness as used in the node.

Validation: scompile.py compiled the delivered module cleanly on the server (1.5 seconds,
nice 19, two threads, 60 seconds per file); no local Lean or Lake was run.
No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by NP

I independently read the node, its nine proof steps, the delivered theorem, the
statement-dependency records, and their source declarations. No statement change,
new definition node, or dependency module is present or needed. The existing Lean
statement is correct and is retained verbatim.

Object, hypothesis, and conclusion checklist (all verdicts: matches):

1. A field k and a projective k-scheme C: `{k : Type u} [Field k]`,
   `{C : Scheme.{u}}`, `p : C ⟶ Spec (.of k)`, `[IsHProjective p]`.
   I opened `IsHProjective.exists_closedImmersion`: it uses a finite-dimensional
   projective space with n+1 coordinates, exactly def-kun-projective. No extra
   Noetherian, reduced, irreducible, perfect-field, or dimension hypothesis appears.
2. Reduced irreducible components of C: `Z`, the integral instances, the closed
   immersions `a`, `hcomponents`, and `hindex`. The latter is a bijection onto
   `irreducibleComponents C`, so all components occur exactly once. I opened
   `irreducibleComponents` (maximal nonempty irreducible subsets), `IsIntegral`
   (nonempty with domain sections on nonempty opens), and
   `reduced_induced_closed_subscheme`, including its uniqueness clause. Integral
   closed subschemes with these images are precisely the reduced induced components;
   these binders present the node's objects rather than impose extra conditions.
3. N and its map to C are the disjoint union of the component normalizations:
   `(Z i).normalization`, `ι`, `hN : IsColimit (Cofan.mk N ι)`, `ν`, and `hν`.
   I opened the upstream absolute normalization and canonical map: they normalize
   an integral scheme in its own function field, with no finiteness assumption.
   I also read the Mathlib discrete-colimit instance, `sigmaOpenCover`, and
   `disjoint_opensRange_sigmaι`. The colimit binder is exactly the required
   coproduct universal property and works for any presentation of the coproduct.
4. Finite and surjective normalization, and finite component set:
   `Finite I ∧ IsFinite ν ∧ Surjective ν`. I read the morphism classes: these mean
   affine with finite affine ring maps, and surjectivity on the underlying space.
   Finiteness is a conclusion, never an input.
5. N projective and proper over k: `IsHProjective (ν ≫ p)` and `IsProper (ν ≫ p)`.
   Both use the original structure morphism. The proper class is separated,
   universally closed and locally finite type (universal closedness supplies
   quasi-compactness), agreeing with the scheme conventions.
6. For each summand: `Nonempty (Z i).normalization`; the explicit conjunction
   `IsDomain` and `IsIntegrallyClosed` for every stalk; and
   `IsIntegral (Z i).normalization`. I read `IsIntegrallyClosed`, whose fraction
   ring definition gives exactly the node's normal-domain condition. Normality
   is asserted on the summands' own local rings, not on C or merely on sections.
7. Each summand open and closed in N: `IsOpenImmersion (ι i)` and
   `IsClosed (Set.range (ι i))`. Together with `hN` this gives exactly the stated
   decomposition; no independent unrelated clopen family is substituted.
8. Each summand projective and proper over k: `IsHProjective` and `IsProper` of
   `(Z i).fromNormalization ≫ a i ≫ p`. By `hν` this is its induced structure map.
9. Conditional dimension bound: `topologicalKrullDim C ≤ 1 → ∀ i, ... ≤ 1`.
   I read `topologicalKrullDim`, defined from chains of irreducible closed subsets
   with values in `WithBot ℕ∞`. The hypothesis stays inside this implication.
10. Factorization through the reduction as its normalization: the existential
    `b` and `νred`, with the three displayed diagram equations. I read
    `nilradical` (the radical of zero), `subscheme`, and `subschemeι`. The first
    equation identifies the same reduced components over the reduction; the
    second factors the given ν; the third specifies νred on the same normalized
    summands. Since the reduction immersion is monic and a homeomorphism on
    spaces, b is automatically a closed immersion with the required component
    image. Thus these equations and hN express normalization of the reduction,
    rather than only existence of some map to the reduction.
11. Empty exactly when C is empty: `(IsEmpty I ↔ IsEmpty C)` is the last clause.

Source review: I read varieties.tex section-normalization and both complete
lemmas 0BXR and 0GK4 with their proofs. The source assumes a field and local
finite type for 0BXR, supplied here by projectivity. It gives finiteness,
normal integral decomposition, and normalization of the reduction; finite
dominant maps are surjective. 0GK4 preserves projectivity and properness.
I also read properties.tex lemma-normal-Noetherian (033M), and algebra.tex
lemma-integral-sub-dim-equal (00OK) and lemma-Noether-normalization (00OY).
These support the node's finite decomposition and dimension argument without
additional hypotheses. The theorem's docstring follows all nine node proof
steps, including the empty coproduct, and carries the source and blueprint id.

Edge cases checked: empty C forces an empty component set by hindex, and hN
then presents the empty scheme N; finite and surjective remain meaningful.
Every summand assertion is vacuous in this case. Zero-dimensional and mixed
zero/one-dimensional components are allowed; no positive-dimension assumption
appears. Arbitrary characteristic, imperfect fields, nonreduced C, and disconnected
C are allowed. There is no n parameter to constrain. `universe u` binds every
universe, and I and all schemes use the same universe as prescribed for scheme
coproducts; the field can be lifted into that universe. No variable is unbound.

Independent reuse searches used different terms from the first reader:

- msearch.py leanfinder: `finite componentwise normalization of proper algebraic
  scheme decomposes into projective normal integral schemes` (eight hits).
  The results concern relative normalization; none is this theorem.
- msearch.py loogle: `IsIntegral, IsProper, IsFinite` (unknown unqualified
  IsProper); repeated as `AlgebraicGeometry.IsIntegral,
  AlgebraicGeometry.IsFinite` (zero hits).
- msearch.py grep: `normalizationCoprodIso|isFinite_fromNormalization|
  normalization_projective_components` (relative-normalization and Zariski-main
  hits). I opened `Scheme.Hom.normalizationCoprodIso`: it concerns a binary
  coproduct in the source of a relative normalization, not reduced components
  of a projective target.
- rg over upstream WeilConjectures, Mathlib AlgebraicGeometry, and project
  lean/Sheaf for `normaliz.*(coprod|component|projective)` and the reverse order,
  plus the exact declaration name. I opened the other pertinent project hits,
  `FiniteGenericCurveModel` and `NormalizationDenseOpen`; their hypotheses and
  conclusions are different. There is no existing declaration to substitute.

No semantic, convention, hollow-definition, or docstring mismatch was found.
No Lean or node edits were necessary. The sole theorem is left with `sorry`;
there are no definitions or proved auxiliary statements. The node's
`lean.statement` was mechanically compared with the signature and is verbatim
equal; all module lines satisfy the 100-character limit.

Second-reader validation: scompile.py passed on the server with no errors or
warnings: the delivered module took 1.5 seconds; its side-only Projective import
took 1.3 seconds. Both used nice 19, two threads, and the 60-second per-file limit.
