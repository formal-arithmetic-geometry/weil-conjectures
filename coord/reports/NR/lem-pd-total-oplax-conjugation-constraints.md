## Worker report

The module `Sheaf.Algebra.Homology.TotalOplaxConjugationConstraints` states
`CategoryTheory.TotalOplaxConjugation.total_oplax_conjugation_constraints` with one
`sorry`. Every other declaration has real defining data and belongs to this node.
No node statement, dependency list, or proof was changed. No new DAG notion was
needed. The helper predicates package the long statement; they assume no extra
compatibility of the square.

Source read: Stacks `sites-cohomology.tex`, Tag 0FPQ,
`lemma-symmetric-monoidal-cat-complexes`, including the degree-zero unit and the
instructions to verify the constraint diagrams. The DAG's ten-step extracted
functor-square calculation supplies the more explicit transport assertion. I read
the entire node, all seven statement dependencies, the proof dependencies, and
the full recorded interfaces, not merely their declaration names.

Hypotheses and constructions, matched to Lean:

- The four categories are `A₀ A₁ B₀ B₁`, with separately bound object and morphism
  universes, `Category`, `Abelian`, `MonoidalCategory`, and
  `MonoidalPreadditive` instances. No braiding, symmetry, flatness, exactness of
  the functors, or boundedness is required.
- Small colimits and their two-sided tensor preservation use
  `HasColimitsOfSize.{w,w}` and `PreservesColimitsOfSize.{w,w}` for both
  `curriedTensor.obj` and `curriedTensor.flip.obj`, with an explicitly bound
  small-diagram universe w. Their standard shrinking instances provide the
  universe-zero interfaces needed for integer-indexed total sums. The countable
  preservation binders quantify universe-zero index types, which represent all
  countable sets up to equivalence; this imposes no restriction on the categories'
  independent object or morphism universes.
- The additive strong monoidal equivalences are `E₀ E₁`, with `Additive`,
  `Monoidal`, and `IsEquivalence`. The functors `Fi Fs` are additive strong
  monoidal, preserving `Discrete I` colimits for every countable `I`. The final
  theorem retains even the separate monoidal structure of `Fs`, which is not
  used to define the conjugated comparison.
- The arbitrary square is `a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs`. There is no `IsMonoidal a`
  hypothesis. Functor composition in Lean is written left to right.
- `CochainComplex _ ℤ` and the imported canonical tensor are the unbounded
  signed direct-sum tensor of the dependency. The canonical total comparison
  is `(G.mapCochainComplexμIso P Q).symm`, and its unit is
  `G.mapCochainComplexεIso.symm`. The ordinary inverse tensorator and unit
  are `(Functor.Monoidal.μIso G M N).symm` and
  `(Functor.Monoidal.εIso G).symm`.
- `tensorIso` is precisely tilde-gamma: first `Fs` of the inverse of the E₀
  oplax tensorator, then inverse `a`, then the Fi and E₁ oplax tensorators,
  then the tensor of `a`. `unitIso` is the displayed tilde-epsilon composite.
- `totalIso` and `totalUnitIso` are precisely the specified A and J, using
  `NatIso.mapHomologicalComplex a` and the same ordered canonical comparisons.
  They are constructed as actual complex isomorphisms, never chosen from
  `Nonempty` and never replaced with the separate Fs comparison.
- `wideTensorIso`, `wideUnitIso`, `wideTotalIso`, and `wideTotalUnitIso` are
  g, e, Â, and Ĵ, formed by prefixing the indicated Fs images of the E₀
  comparisons. The removed comparisons remain explicit and invertible.

`SmallColimitConjugationConstraints`, the theorem's conclusion, installs only
Mathlib's canonical `hasColimitsOfSizeShrink` and
`preservesSmallestColimits_of_preservesColimits` in its defining body and then
returns `ConjugationConstraints`. No `let` occurs in a theorem signature, and no
new proof obligation or extra universe-zero hypothesis is introduced.

Clauses of `ConjugationConstraints`, in order:

1. Every `p q n h` inverse summand restriction is exactly the displayed
   `ι' ≫ A.inv.f n = tildeGamma.inv ≫ Fs.map ι`, using the two termwise E₀
   complexes and their canonical `HomologicalComplex.ιTensorObj` inclusions.
2. Both inverse equations are equalities of complex morphisms, not just of
   their degree components.
3. The inverse chain equation is recorded for every pair `n m`; the source
   differential is Fs applied termwise to the canonical signed total and the
   target differential is its canonical signed total. Thus it also covers
   every non-adjacent (zero) differential.
4. The degree-zero J component, conjugated by `singleObjXSelf` identifications,
   is `unitIso.hom`, exactly tilde-epsilon.
5. Every nonzero-degree J component is zero. Its source and target are zero
   objects since additive functors preserve zero objects; therefore this is
   the unique map specified by the node.
6. `ConstraintRestrictions` is instantiated with `G = E₀ ⋙ Fs` and the four
   *specified* wide comparisons, not arbitrary comparison maps.

Clauses of `ConstraintRestrictions`, in order:

- The binary restriction of Â is `G.map ι ≫ T.hom.f = g.hom ≫ ι`.
- `leftι` is the left-nested ordinary triple inclusion and `rightι` is the
  right-nested inclusion at degree `p+q+r`. The source reassociation restriction
  explicitly records `G(αCh) G(leftι) = G(rightι) G(α)`.
- The first outer T comparison has its separate restriction along `rightι`,
  including `G` of the inner Q,H inclusion. `associatorPath₁` then has precisely
  the node's first ordinary path `G(α) ≫ g ≫ (1 ⊗ g) ≫ rightι`.
- The second outer T comparison has its separate restriction along `leftι`,
  including `G` of the inner P,Q inclusion. A further clause records the stage
  after `T P Q ⊗ 1`, before the target associator. `associatorPath₂` then
  restricts to `g ≫ (g ⊗ 1) ≫ α ≫ rightι`.
- Ĵ in degree zero is e, with canonical single-complex identifications.
- For each of the left and right units the direct path is `G` of the ordinary
  unitor. The transported path has a separate restriction after T, another
  after the unit comparison tensor identity, and the full restriction after
  the target unitor. These yield respectively `g ≫ (e ⊗ 1) ≫ λ` and
  `g ≫ (1 ⊗ e) ≫ ρ`, at degrees `(0,n)` and `(n,0)`.
- For unit degree `k ≠ 0`, both direct and transported paths restrict to zero,
  quantified over every total degree and complementary degree.
- Binary, nested triple, left-unit and right-unit inclusions determine complex
  morphisms with arbitrary target complex. No finite-support restriction or
  finite-sum replacement appears. All integer degrees are quantified.
- Finally the three implications state exactly that equality of the ordinary
  associator/left-unit/right-unit paths implies equality of the corresponding
  whole total paths. The implications are separate, so no unnecessary joint
  ordinary-coherence hypothesis is imposed.

The original A,J path assertion is encoded by the node's explicit Â,Ĵ formulation:
all four wide comparisons are *defined* by prefixing the specified E₀ comparisons
to A,J. Removing those isomorphisms recovers A,J and tilde-gamma/tilde-epsilon,
including the intermediate comparison maps. No equality with the Fs tensorator
is asserted.

Dependency declarations used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Monoidal.Category`: `MonoidalCategory`, its ordinary
  associator/unitors, `tensorIso`.
- `Mathlib.CategoryTheory.Monoidal.Functor`: `Functor.Monoidal`, `μIso`, `εIso`,
  implementing the recorded `CoreMonoidal` notion with both inverse maps.
- `Mathlib.CategoryTheory.Limits.HasLimits`: chosen colimits, `HasColimitsOfSize`;
  `Mathlib.CategoryTheory.Limits.Preserves.Basic`: preservation classes.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: complex category through the
  imported dependency (no derived localization is used in this statement).
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`: the recorded signed
  binary total interface; no K-flatness assumption is introduced.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`:
  `HomologicalComplex.monoidalCategory`, canonical complex constraints.
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`:
  `Functor.mapCochainComplexμIso`, `Functor.mapCochainComplexεIso`, with their
  recorded summand, naturality and coherence lemmas. This proof dependency is
  imported publicly because the statement's actual constructions use it.
- `Mathlib.Algebra.Homology.Additive`: `NatIso.mapHomologicalComplex`.
- `Mathlib.CategoryTheory.Adjunction.Limits` is the proof-only import for the
  equivalences' colimit preservation.
- The proof-only conjugation-summands node has no recorded module yet, so no
  nonexistent module is imported and its statement is not duplicated here.

Edge cases checked mathematically: zero complexes; complexes supported only in
one negative degree; all integer decompositions of a fixed total degree; the
unit at degree zero and its off-zero summands; infinite two-sided complexes;
identity equivalences and identity functors with an arbitrary scalar natural
automorphism a=c. In that example g=c and e=c⁻¹, so both associator paths carry
c² and unit paths carry c⁻¹c. Thus no accidental monoidality hypothesis is hidden.
Independent universes are bound explicitly and `autoImplicit` is false.

Searches actually run for this delivery:

- `msearch.py leanfinder`: "Inverse and associator unitor path restrictions of
  total tensor comparison conjugated through a natural isomorphism of strong
  monoidal functors". Eight hits, including `coreMonoidalTransport_μIso_inv` and
  abstract monoidal inverse lemmas; none gives these total summand/path formulas.
- `msearch.py loogle`: "Functor.Monoidal, HomologicalComplex, tensorObj" returned
  unknown identifier `Functor.Monoidal`; this was not treated as a no-match search.
  Repeated with "HomologicalComplex, CategoryTheory.Functor.OplaxMonoidal":
  successful, zero hits.
- `msearch.py leansearch`: "Total tensor comparison conjugated by a natural
  isomorphism has inverse and associator and unitor path restrictions on each
  coproduct summand". Eight generic coproduct/monoidal/unitor hits; no exact match.
- `msearch.py grep`: "conjugat|mapCochainComplexμIso", subdirectory
  `CategoryTheory/Monoidal`: 19 generic conjugation hits, no complex path theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for total/conjugation and
  oplax-conjugation patterns, and literal-node-id grep in WeilConjectures: no
  exact generic theorem. The specialized section comparison modules were read
  and reuse their own specialized objects, not a generic four-category square.
- Read upstream `MapHomologicalComplex.lean` in full and the recorded dependency
  signatures/docstrings. Existing canonical totals are reused throughout.

No STATEMENT-DISPUTED flag, statement correction, dependency repair, or new node.
The module compiles with the prescribed `scompile.py`; final dry-run results are
recorded after its completion.

## Second reading by NR

This dispatcher forbids starting other agents and assigns independent review to
the maintainer. This section records my separate second pass, not an independent
agent review. I reread the node and module side by side, tracing every composite
from right-to-left mathematical composition to Lean's left-to-right `≫`.
The initial pass exposed a shadowed `tensorIso` name and loss of the dependent
countable-preservation instance in `wideTotalIso`; these were repaired by the
qualified `MonoidalCategory.tensorIso` and explicit `(hFi := hFi)` argument.
The next pass found that complete unitor paths alone did not explicitly list
their intermediate comparisons. I added both intermediate equations on each
side. The theorem retains Fs's monoidal and countable-preservation hypotheses,
although its canonical conjugation does not use the separate Fs tensorator.
The final pass generalized the four colimit assumptions from universe zero to
an explicitly bound w. The total-tensor instance search does not automatically
shrink arbitrary diagram universes, so I added the definition
`SmallColimitConjugationConstraints` that applies Mathlib's actual shrinking
constructions and uses the existing proposition, with no additional assumptions.
I then checked the inverse direction, both chain inverse equations,
zero-degree single-complex identifications, the two different triple nesting
orders, and the off-zero unit summands against the node's formulas. No change
to the mathematical statement was made; the maintainer's independent reading
remains the delivery review.

Validation: final `scompile.py` compiled both the sandbox and real module name
cleanly (58.1 s and 41.7 s compiler timings, within the unchanged 60 s limits).
`deliver2.py ... --no-push` printed `OK (dry run)` for commit `464a4a4a8a6`:
preflight passed and the delivery compiled. The packet contains exactly the
module, the item's node copy, and this report.
