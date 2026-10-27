# Profinite.scalarCechTuples and Profinite.scalarCechDelete

## Reason

The finite-coefficient and inverse-limit primitive modules publicly imported the exactness
module to obtain only its tuple definitions. Exactness must import these two lemmas, so
this arrangement would create a cycle. Move the two definitions verbatim to
Sheaf.Topology.ProfiniteCechTuples. The original module publicly reexports the new module.
Both primitive modules now publicly import the definition module instead of the theorem.
Both adapted primitive modules are unclaimed according to coord/claims at
preparation time. The assigned exactness module is held by X9.

## Old

In Sheaf.Topology.NormedScalarProfiniteCechExact:

```lean
abbrev scalarCechTuples {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) :=
  {t : Fin r → T // ∀ i j : Fin r, q (t i) = q (t j)}

/-- Delete coordinate `j`, retaining the equal-image condition.
Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), explicit Cech expansion in the DAG
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact). -/
def scalarCechDelete {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) (j : Fin (r + 1))
    (x : scalarCechTuples q (r + 1)) : scalarCechTuples q r :=
  ⟨fun i ↦ x.val (j.succAbove i), fun i k ↦ x.property (j.succAbove i) (j.succAbove k)⟩

```

## New

Identical declarations, in Sheaf.Topology.ProfiniteCechTuples:

```lean
abbrev scalarCechTuples {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) :=
  {t : Fin r → T // ∀ i j : Fin r, q (t i) = q (t j)}

/-- Delete coordinate `j`, retaining the equal-image condition.
Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), explicit Cech expansion in the DAG
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact). -/
def scalarCechDelete {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) (j : Fin (r + 1))
    (x : scalarCechTuples q (r + 1)) : scalarCechTuples q r :=
  ⟨fun i ↦ x.val (j.succAbove i), fun i k ↦ x.property (j.succAbove i) (j.succAbove k)⟩

```

The exactness module adds `public import Sheaf.Topology.ProfiniteCechTuples`.
FiniteCoefficientCechPrimitiveLift and InverseLimitCechPrimitive replace their public
import of NormedScalarProfiniteCechExact by ProfiniteCechTuples. They retain every
existing declaration and proof unchanged. Their public statements use only the tuple
interface; they do not need the normed exactness theorem or its coefficient imports.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Topology.NormedScalarProfiniteCechExact | X9 | Reexports definitions; proves its existing theorem using the primitive lemmas. |
| Sheaf.Topology.FiniteCoefficientCechPrimitiveLift | unclaimed | Public import points to definitions; signatures and proofs unchanged. |
| Sheaf.Topology.InverseLimitCechPrimitive | unclaimed | Public import points to definitions; signatures and proofs unchanged. |
| Sheaf.Topology.NormAlgclProfiniteCechExact | unclaimed | Receives identical tuple definitions through original public import. |
| Sheaf.Topology.FiniteNormedScalarSectionAcyclicity | unclaimed | Existing exactness theorem and public coefficient imports remain available. |

The downstream.py queries were run for the original module and for each primitive
module, including --uses Profinite.scalarCechTuples. No mathematical definition or
target statement changes. No weakened statement or extra hypothesis is introduced.

## Status

landed 20261025T071241-L-161674 2026-10-25 (merge of deliver/X9/Sheaf.Topology.NormedScalarProfiniteCechExact)
