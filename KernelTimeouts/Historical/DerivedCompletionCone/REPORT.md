# Derived-Completion Cone

## Environment and exact declaration

The inline baseline is the `derivedCompletionCone` source introduced by `9ba4d01f55c`
before the named-diagram fix. The control is `fe5f5d78f1c`. Both use Lean
`leanprover/lean4:v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
The imported module is `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.

```lean
noncomputable def DerivedCategory.derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) :=
  sorry
```

The successful source first defines
`DerivedCategory.derivedCompletionDiagram J I K := DerivedCategory.quotPowFunctor J I ⋙
tensorLeft K` and uses `Cone (derivedCompletionDiagram J I K)` in the declaration.

## B1.1 Phase split

| Operation | Inline baseline | Named control |
| --- | ---: | ---: |
| elaboration with `debug.skipKernelTC` | 17.7 s | 17 s |
| `Kernel.check(type)` | 3 ms | fast |
| `Kernel.check(value)` | 3 ms | fast |
| final inferred/declaration conversion | `>600 s`, terminated | approximately free |
| real inline value | `>7 min`, terminated | 9.5 s with named diagram |

The `sorry` row is a diagnostic isolation: it is not a successful proof. An axiom with the
same inline type checks in 6.7 s, and the same expression placed in a trivial `Type` value
checks in 5.3 s. Thus the type expression and value check are individually cheap; the
expensive operation is the conversion performed while adding a definition.

## B1.2 `abstractNestedProofs` output

The inferred type of the value is structurally different from the declared type. A
structural diff finds 36 minimal differing positions, every one a proof. Representative
pairs are:

| Inferred/value side | Declared/type side | Proposition family |
| --- | --- | --- |
| `DerivedCategory.quotPowFunctor._proof_1` | `GrothendieckTopology.hasSheafify_of_essentiallySmall` | `HasSheafify` |
| `DerivedCategory.quotPowFunctor._proof_2` | `GrothendieckTopology.isGrothendieckAbelian_sheaf_of_essentiallySmall` | sheaf Grothendieck abelianity |
| `derivedCompletionDiagram._proof_1` | `instIsGrothendieckAbelianModuleCat` | abelian instance |
| `derivedCompletionDiagram._proof_3` | `CategoryTheory.Sheaf.monoidalPreadditive` | monoidal preadditivity |
| `derivedCompletionDiagram._proof_8` | `DerivedCategory.hasDerivedMonoidalCategory` | K-flat derived monoidal structure |

The proof terms themselves are propositionally irrelevant. Their proposition types are not
cheap: those types carry concrete category and monoidal instance arguments. This is direct
structural-diff evidence; the exact recursive fan-out inside proof irrelevance remains an
inference because no patched kernel trace was committed.

## B1.3 Proof-body versus proposition-type controls

The proof-free value control (`E21`) has the same inline declared type and completes in 5.2 s;
the `sorry` declaration still times out. Removing proof construction therefore removes the
conversion only when it also removes nested proof abstraction. The real issue is the types in
which the proofs live, not construction of the proof bodies. A typed `sorry` value is a
diagnostic control, never a successful proof.

## B1.4 Concrete `MonoidalCategory` expressions

The relevant inferred type contains, after explicit printing, an instance of the shape:

```text
DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Sh catSh abSh ⟨IsGrothendieckAbelian⟩ hasDerivedSh
  (monoidalCategory_sheaf_of_essentiallySmall ...)
  (monoidalClosed_sheaf_of_essentiallySmall ...)
  ⟨MonoidalPreadditive⟩
  (braidedCategory_sheaf_of_essentiallySmall ...)
  ⟨Qh.HasDerivedMonoidalCategory⟩
```

The `monoidalCategory_sheaf...` and `braidedCategory_sheaf...` paths use the ambient
`instBraidedCategory`, while the `monoidalClosed...` path is supplied through the ambient
`symmetricCategory`. The outer derived monoidal instance is data-valued and carries the
proofs listed above. The first causal divergence is therefore an instance expression inside
the proposition types of nested proofs, not the cone data itself.

## B1.5 Explicit instance control

| Variant | Instance source | Result | Reading |
| --- | --- | ---: | --- |
| B-I0 | inferred concrete derived `MonoidalCategory` | `>600 s` inline | baseline |
| B-I1 | explicit local `MonoidalCategory` parameter | 18 s | large concrete instance is causal |
| B-I2 | shared local instance on both sides | same fast family | sharing stabilizes the comparison context |
| B-I3 | separately constructed but definitionally equal instances | not a successful independent proof of identity; no claim made | identity versus definitional equality is unresolved |

The 18 s row is direct. It is not evidence that every explicit instance is fast: the
important change is that both sides now use one local variable, moving the proof-laden
construction out of the comparison. The earlier control that only aligned the braided versus
symmetric ambient argument still OOM-killed after 8 m 24 s, so that mismatch is not the main
cause.

## B2.1 Diagram representation matrix

| Variant | Diagram in cone type | Result |
| --- | --- | ---: |
| B-D0 | fully inline `quotPowFunctor ⋙ tensorLeft K` | `>600 s` |
| B-D1 | named `abbrev` | approximately 17 s |
| B-D2 | named ordinary `def` | fast named-boundary family |
| B-D3 | named reducible definition | fast named-boundary family |
| B-D4 | expanded named body at use site | timeout path returns |

D0 and D1 are the historical diagnostic pair. D2/D3 are representation controls: the
observed benefit is the complete named head in the declared type, not a promise that every
reducibility annotation behaves identically. D4 deliberately punctures the boundary.

## B2.2 Naming versus sharing

Naming changes the outer expression in the declared type to the common head
`DerivedCategory.derivedCompletionDiagram` applied to `J`, `I`, and `K`. The body still
unfolds to the inline diagram when it is checked. The conversion no longer compares two
proof-laden reconstructed instance expressions at every cone declaration. This establishes a
comparison boundary; it does not establish a kernel cache mechanism. A separately written
inline expression is definitionally equal but does not preserve the same declared boundary,
and D4 reproduces the timeout.

## B3. Factorial test

| Variant | Diagram | Instance | Result |
| --- | --- | --- | ---: |
| B00 | inline | inferred concrete | `>600 s` |
| B10 | named `abbrev` | inferred concrete | about 17 s |
| B01 | inline | explicit local parameter | 18 s |
| B11 | named diagram | explicit local parameter | 5.3 s for the complete API; 9.5 s with real cone term |

Both factors help, and the combined control has the smallest measured cost. The result is
interaction between a diagram boundary and an instance-sharing boundary, not a single
reducibility switch.

## B4 Conversion tree and footprint

```text
derivedCompletionCone declaration
└─ final inferred-type / declared-type conversion
   ├─ cone/functor application
   ├─ derivedCompletionDiagram / inline diagram argument
   ├─ concrete derived MonoidalCategory argument
   └─ 36 nested proof-position proposition comparisons
      └─ HasSheafify, Grothendieck abelianity, MonoidalPreadditive,
         HasDerivedMonoidalCategory and dependent instance arguments
```

The parent conversion dominates. `Cone`, `Functor.comp`, and the quotient-power tower are
fast controls. The 337-node shared DAG (6,217 without sharing) is only modestly larger than
the abstract `Cone F` control (269 / 2,427), so term size is not the explanation. The
reduction footprint is the fan-out through concrete instance propositions; the named diagram
and explicit-instance controls remove that descent. Inclusive parent and child costs are not
added.

## §6/§7 controls and classification

| Hypothesis/control | Result |
| --- | --- |
| elaboration/typeclass synthesis is the bottleneck | ruled out by 17.7 s kernel-skip run |
| `Cone`, `Functor.comp`, quotient tower are intrinsically slow | ruled out by E5 controls |
| expression size/sharing is sufficient explanation | ruled out by 337-node size |
| braided/symmetric mismatch alone | ruled out by E12 OOM result |
| concrete derived monoidal instance matters | confirmed by 18 s explicit-instance control |
| proof bodies alone matter | ruled out by proof-free and typed controls |
| named diagram removes the problematic final conversion | confirmed by the real 9.5 s construction |

**R1/R2:** The exact cost site is the final inferred/declaration conversion. The candidate
boundary is the diagram head plus the concrete derived `MonoidalCategory` argument.

**R3/R4:** The exposed structure is the proof-carrying derived monoidal instance and its
dependent proposition fields. One final conversion dominates; 36 related proof positions
fan out inside it rather than appearing as independent declaration checks.

**R5/R6:** Naming the diagram and sharing the instance reduce the same obligation while
preserving the real cone term; the timeout returns when the inline type is restored.

**R7:** Classification **P2/H2**, with **H3** as a secondary repeated proof-position effect;
confidence **confirmed** for phase and causal boundary, **strongly supported** for the exact
proof-proposition fan-out. The exact internal branch ordering remains open.

## Round-two fresh measurements

The fresh source files are `probes/round2/B-inline.lean`, `B-named.lean`, and
`B-explicit-instance.lean`. Each was run with
`timeout 3600 /usr/bin/time -v lake env lean -Dbackward.isDefEq.respectTransparency=false
-DmaxSynthPendingDepth=3 <probe>`.

| Variant | Fresh result | Peak RSS |
| --- | --- | ---: |
| Inline `Cone (quotPowFunctor J I ⋙ tensorLeft K) := sorry` | deterministic kernel timeout at 118.66 s; exit 1 | 13,826,340 kB |
| Named `Cone (derivedCompletionDiagram J I K) := sorry` | succeeds; 2.27 s wall | 3,741,412 kB |
| Inline with explicit local `MonoidalCategory` parameter | succeeds; 2.35 s wall | 3,741,488 kB |

The inline timeout is the direct B1.1 reproduction on the v4.33.1 historical toolchain.
The named and explicit-instance rows are fresh controls. The earlier `>600 s`, 18 s,
and 9.5 s values are historical notes from the first pass, not round-two measurements.

The fresh hint probe reports the three scratch diagram declarations as regular definitions
with height 31. The historical source's 36 proof-position differences, auxiliary proof
names and proposition types, concrete `MonoidalCategory` expression dump, factorial
matrix, and conversion tree were not re-generated in round two; those sections are
retained as historical notes rather than new numerical evidence.

The fresh matrix probe `probes/round2/B-matrix.lean` compiled the named `abbrev`, named
ordinary `def`, named reducible `def`, shared-but-unnamed inline, and named-plus-explicit
instance declarations together in 2.43 s wall time (3,743,452 kB peak RSS). Thus the
four B3 cells are represented by fresh compilations: B00 is the separate 118.66 s
timeout, B10 is the 2.27 s named inferred-instance run, B01 is the 2.35 s explicit
inline run, and B11 is present in the matrix compilation and completes within its
2.43 s process. The matrix process does not provide isolated per-declaration timings;
the isolated B10/B01 values above are the preferred timings.
