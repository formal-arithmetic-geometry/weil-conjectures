## Worker report

The module Sheaf.AlgebraicGeometry.FiniteGenericRadicialSmoothing states
AlgebraicGeometry.exists_finite_generic_radicial_smoothing, with sorry as the whole
proof. No definitions, auxiliary theorems, new nodes, dependency repairs, or statement
corrections were needed.

Clause correspondence:

- A field is `(k : Type u) [Field k]`. The base is `(S : Scheme.{u}) [IsIntegral S]`.
  Its structure over k is `[S.Over (Spec (.of k))]`; finite type is
  `[LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]`.
- The finite type family is `(X : Scheme.{u}) (f : X ⟶ S)` with
  `[LocallyOfFiniteType f] [QuasiCompact f]`. Nonemptiness is `[Nonempty X]`.
- The optional sheaf is `F : Option (Sheaf X.smallEtaleTopology (Type (u + 1)))`.
  `none` states the assertion without a sheaf, and `some E` states its refinement
  for E. The hypothesis `∀ E ∈ F, Scheme.IsConstructibleEtaleSheafOfSets E`
  requires precisely constructibility when supplied. This recorded constructibility
  predicate includes finite local constancy on each stratum, so includes finiteness.
  Option only bundles the two cases; it imposes no new condition on the sheaf.
- Shrinking is `∃ U : S.Opens, (U : Set S).Nonempty ∧ ...`.
- The finite radicial surjection is `∃ (T : Scheme.{u}) (q : T ⟶ U.toScheme),
  IsFinite q ∧ UniversallyInjective q ∧ Surjective q ∧ ...`. UniversallyInjective
  is radicial by Stacks 01S4, as fixed by the scheme conventions dependency.
- The base change is `pullback f (q ≫ U.ι)`. Its reduction is exactly
  `(pullback f (q ≫ U.ι)).nilradical.subscheme`, using the recorded reduction.
- V is an open of that reduction, with `Dense (V : Set ...)` and
  `Smooth (V.ι ≫ ...nilradical.subschemeι ≫ pullback.snd f (q ≫ U.ι))`.
- The sheaf conclusion is `∀ E ∈ F, Scheme.IsLocallyConstantEtaleSheafOfSets
  ((Scheme.etaleSetPullback (V.ι ≫ ...nilradical.subschemeι ≫
  pullback.fst f (q ≫ U.ι))).obj E)`. This is the canonical inverse image
  from X directly to V; it includes base change, reduction and open restriction.
- `∀ η : T, IsGenericPoint η Set.univ → ...` specifies the generic fibre without
  choosing its generic point or adding an integrality condition on the cover.
  The generic-fibre complement is the subtype of reduced-pullback points y with
  `(...subschemeι ≫ pullback.snd ...) y = η ∧ y ∉ V`. The scheme fibre and this
  subspace agree by Mathlib's `Scheme.Hom.fiberHomeo`; complement and components
  therefore have exactly the topology in the node.
- For every `Z ∈ irreducibleComponents` of that complement and every
  `C ∈ irreducibleComponents` of the original unreduced pullback, the inclusion
  clause `∀ z ∈ Z, ...nilradical.subschemeι z.1 ∈ C` expresses containment under
  reduction. The conclusion is `topologicalKrullDim Z < topologicalKrullDim C`.
  C is not a component of a different space or of just the generic fibre.

Statement dependencies used:

- def-weil-pbc-scheme-conventions is a convention-only record. Its Mathlib notions
  are LocallyOfFiniteType, QuasiCompact, IsFinite, UniversallyInjective and Surjective;
  no new convention predicate is introduced.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme (and its public Basic import):
  Scheme.nilradical, Scheme.IdealSheafData.subscheme and subschemeι.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- WeilConjectures.AlgebraicGeometry.EtaleSheaves:
  Scheme.IsConstructibleEtaleSheafOfSets, Scheme.etaleSetPullback,
  Scheme.IsLocallyConstantEtaleSheafOfSets. Read the published current source with
  `scompile.py --source`, since the old upstream checkout lacks this module.
- WeilConjectures.Mathlib.Topology.KrullDimension and its Mathlib public import:
  topologicalKrullDim (topologicalKrullDimAt is the dependency's other recorded notion).

The available modules of all proof dependencies are imported without public import.
The theorem docstring carries all five steps of the node's natural-language proof.
The finite-type, finite-component and flat-open Mathlib matches are also imported.

Edge cases checked: the field has arbitrary characteristic; no perfection assumption.
The base cannot be empty by IsIntegral and the shrink is explicitly nonempty. X is
initially nonempty, but need not dominate S: a shrinking may remove all of X, and
V may then be empty (dense in the empty pullback). No Nonempty V is required.
Empty generic fibres and empty complements have no irreducible components, so the
last assertion is vacuous. Zero-dimensional containing components cannot contain a
component of the generic complement, exactly as the strict inequality requires.
No equidimensionality, irreducibility of X, geometric irreducibility of fibres,
affineness, separatedness, positive characteristic, or reducedness of T is imposed.
All schemes and k use universe u, and the sheaf takes values in Type (u+1), as in
the recorded dependency. All universes and variables are explicitly bound.

Searches for an existing statement:

- msearch.py leansearch: `Finite radicial base change with dense smooth open and
  constructible sheaf locally constant`: service unavailable, Internal Server Error;
  no hits returned. This failed search is not evidence of absence.

- msearch.py leanfinder: `Finite radicial base change dense smooth open reduction
  finite type integral base`: eight hits, including Algebra.Smooth.exists_finiteType,
  smooth algebra descent and standard smooth chart lemmas; none state the result.
- msearch.py loogle: `AlgebraicGeometry.UniversallyInjective,
  AlgebraicGeometry.Smooth`: zero hits.
- msearch.py grep: `generic.*smooth|smooth.*generic` in AlgebraicGeometry:
  four hits in Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean concerning smoothness
  at generic points over a perfect field; these do not provide the radicial cover,
  the constructible sheaf assertion or the component dimension comparison.
- rg over upstream WeilConjectures and project lean/Sheaf:
  `radicial|generic_radicial|genericRadicial|lem-fin-generic-radicial-smoothing`
  and `generic.*smooth|smooth.*generic|exists.*smooth.*open`. Found preparation
  lemmas and downstream proof-docstring references, no existing exact theorem.
  In particular GenericGeometricallyReducedPreparation gives flatness and geometric
  reducedness, but does not give the requested dense smooth open and sheaf refinement.

The statement agrees with the blueprint source; no statement dispute was found.
Compilation with the required scompile.py wrapper passed cleanly. The final dry-run
result is recorded by deliver2.py; the second reader supplies the independent reading.


## Second reading by ND

I independently read the sandbox node and complete Lean module against the blueprint
source sec-smooth-purity/sk-prop-sf-cbc/lem-fin-generic-radicial-smoothing.md. I also
read Stacks more-morphisms.tex, lemma-make-generic-fibre-geometrically-reduced (0550),
and varieties.tex, lemma-geometrically-reduced-dense-smooth-open (056V). The former
assumes only an irreducible base and finite type morphism; the latter assumes a
reduced scheme locally of finite type over a field. Neither adds a perfect-field,
separatedness, dominance, or geometric-irreducibility assumption. The node's five-step
proof supplies precisely these inputs. There is no statement_change to audit.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Base field: `(k : Type u) [Field k]`. PASS: arbitrary field, any characteristic.
2. Integral base scheme: `(S : Scheme.{u}) [IsIntegral S]`. PASS: Mathlib's recorded
   IsIntegral includes nonemptiness and integral-domain sections on nonempty opens;
   no separate Noetherian or affine hypothesis is added.
3. Finite type over that field: `[S.Over (Spec (.of k))]` with
   `[LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]`.
   PASS: exactly the convention node's finite type, with the actual structure map.
4. Family: `(X : Scheme.{u}) (f : X ⟶ S)` and
   `[LocallyOfFiniteType f] [QuasiCompact f] [Nonempty X]`. PASS: exactly finite type
   and X nonempty, without smoothness, reducedness, irreducibility, or dominance.
5. Optional constructible finite sheaf on X:
   `(F : Option (Sheaf X.smallEtaleTopology (Type (u + 1))))` and
   `(hF : ∀ E ∈ F, Scheme.IsConstructibleEtaleSheafOfSets E)`.
   PASS: none gives the sheaf-free assertion; some E gives the assertion for each
   prescribed constructible finite sheaf E. The witnesses may depend on E, as they
   may in the source. Read the current EtaleSheaves and FiniteLocallyConstantSets
   modules through scompile --source: constructibility uses a finite stratification
   with finite locally constant inverse images, not just local constancy. Thus no
   missing finiteness hypothesis or abelian coefficient structure is hidden here.
6. Shrinking: `∃ U : S.Opens, (U : Set S).Nonempty ∧ ...`. PASS: a genuine nonempty
   open of the original base, not a shrinking only on the cover.
7. Cover: `∃ (T : Scheme.{u}) (q : T ⟶ U.toScheme), IsFinite q ∧
   UniversallyInjective q ∧ Surjective q ∧ ...`. PASS: exactly finite, radicial,
   and surjective. UniversallyInjective is the convention's equivalent radicial
   notion. Integrality or affineness of T is not demanded in the conclusion.
   A finite radicial surjection is a homeomorphism on spaces, so T is nonempty
   irreducible and sober and has a generic point. The later universal generic-point
   clause cannot be evaded by choosing a cover without a generic point.
8. Base change and reduction: `(pullback f (q ≫ U.ι)).nilradical.subscheme`.
   PASS: the canonical fibre product X times_S T and its actual reduction; read
   Scheme.nilradical = radical bottom, IdealSheafData.subscheme, and subschemeι.
9. Dense smooth open: `∃ V : ...subscheme.Opens, Dense (V : Set ...) ∧
   Smooth (V.ι ≫ ...subschemeι ≫ pullback.snd f (q ≫ U.ι)) ∧ ...`.
   PASS: density in the entire reduced pullback, and smoothness of its actual
   structure map to T. Smooth is the dependency's affine-local smooth ring-map
   predicate, not merely smoothness at selected points or over the original base.
10. Sheaf refinement: `∀ E ∈ F, Scheme.IsLocallyConstantEtaleSheafOfSets
    ((Scheme.etaleSetPullback (V.ι ≫ ...subschemeι ≫ pullback.fst ...)).obj E)`.
    PASS: inverse image along the canonical map V to X. The dependency builds it
    by left Kan extension along etale base change and sheafification; this includes
    base change, reduction and restriction, with no arbitrary morphism supplied.
11. Generic fibre: `∀ η : T, IsGenericPoint η Set.univ → ...` and the subtype
    `{y : ...subscheme | (...subschemeι ≫ pullback.snd ...) y = η ∧ y ∉ V}`.
    PASS: this is exactly the complement of V in the generic fibre. I read
    Scheme.Hom.fiberHomeo: it identifies the scheme fibre with the point preimage
    using the fibre immersion. The induced complement topology therefore agrees.
12. Componentwise dimension: for every `Z ∈ irreducibleComponents _` of that
    complement, and every `C ∈ irreducibleComponents ↥(pullback f (q ≫ U.ι))`
    containing the image of Z under subschemeι, the conclusion is
    `topologicalKrullDim Z < topologicalKrullDim C`. PASS: the ambient C belongs
    to the unreduced total pullback, exactly as the node says. Containment uses
    `∀ z ∈ Z, ...subschemeι z.1 ∈ C`, and both dimensions use subtype topology.
    I read the recorded topological dimension declarations: topologicalKrullDim
    is Krull dimension of irreducible closed sets, with empty-space value bottom.

Dependency audit: opened all six stmt_deps records and their signatures, including
scheme conventions (which intentionally has no declaration). Read the actual
Mathlib definitions of IsIntegral, LocallyOfFiniteType, QuasiCompact, IsFinite,
UniversallyInjective, Smooth, nilradical/subscheme/subschemeι, and topologicalKrullDim,
and the published current set-sheaf predicates and pullback. These are exactly the
recorded notions. No new definition node or dependency module is delivered.
The generic preparation module's signature was also checked against 0550: it
supplies the reduced pullback, finite universal homeomorphism, integral affine
cover, flat finite presentation and geometrically reduced generic fibre used by
proof steps 1 and 2. The existing GenericRadicialGeometricallyReducedModel is an
other theorem: it requires an affine source and geometrically irreducible generic
fibre, and does not state this smooth-open/sheaf/dimension conclusion.

Edge cases: IsIntegral excludes the empty base, and Nonempty X is precisely the
stated starting assumption. X need not dominate S, so after shrinking the entire
pullback and V may both be empty; Dense does not force Nonempty V. Empty generic
fibres or empty complements have no irreducible components and give vacuous final
clauses. A zero-dimensional C cannot contain a component of the complement, as
required by the strict inequality. The optional sheaf also allows empty stalks
and the no-sheaf case. Characteristic zero and imperfect positive-characteristic
fields are both covered. There is no numerical n or index set requiring positivity.
The schemes and field use arbitrary universe u; the set-valued sheaves use the
recorded site's Type (u+1) convention. Smaller data can be regarded in a common
universe; no universe equality for independent sites or coefficients is assumed.
All variables and the universe are bound explicitly.

Independent duplicate searches (2026-10-15), using different search terms:

- msearch leanfinder: `finite purely inseparable alteration generically smooth
  reduced scheme dense open`: eight hits, including IsGeometricallyReduced,
  FormallySmooth.of_perfectField, standard smooth chart existence, and smoothLocus.
  None gives the finite radicial cover plus open, sheaf and dimension conclusions.
- msearch loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Smooth`: zero hits.
- msearch leansearch: `A finite radicial cover of an integral base yields a dense
  smooth open in the reduced base change`: unavailable (Internal Server Error).
  This failed service is not evidence of absence.
- rg across Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf:
  `radicial|purely.inseparable.*smooth|smooth.*purely.inseparable|generic.*smoothing|
  smoothing.*generic`. Found the generic radicial preparation family and references
  in downstream GenericOpenImmersionConstructibility, but no matching statement.
  Exact-name search for exists_finite_generic_radicial_smoothing in the upstream
  name table and both source trees returned no hit.

No mismatch was found. The correct Lean signature, node statement and proof docstring
were retained verbatim; this reading adds only this report and independent searches.
H5/H6: there are no new definitions or helper theorems; the single theorem has sorry
as its entire proof. H8: both docstrings name the blueprint source and node, and
all five proof steps and their dependencies are present. H9: no private or local
notation, hidden universes, custom instances, or lines over 100 characters.
Compilation and final dry-run results are checked below before delivery.

Independent scompile.py compilation: PASS, no errors or warnings. Both sandbox
and library-path checks passed (3.3 s and 3.5 s). Checked exact signature equality
against lean.statement programmatically and all Lean lines are at most 100 characters.

Required deliver2.py --no-push: OK; preflight and compilation passed, nothing pushed.
