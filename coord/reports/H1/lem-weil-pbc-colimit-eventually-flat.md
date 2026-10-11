## Worker report

The module `Sheaf.RingTheory.ColimitEventuallyFlat` introduces the data structure
`RingTheory.ColimitEventuallyFlatData` and states `RingTheory.exists_flat_stage`.
The structure records a nonempty directed preorder, stage rings `A` and `B`, stage
modules `N`, commutative-ring/additive/module instances, local and Noetherian
hypotheses, finite generation, structure and transition maps, identity and
composition compatibility, locality, scalar compatibility, ring/module colimit
conditions, localization, tensor base change, and flatness of the colimit.
The theorem concludes that some stage module is flat over its stage `A` ring;
the `letI` binders render the relevant commutative-ring, module, and scalar
restriction structures explicitly. Every field of the node's hypotheses is
represented by a correspondingly named structure field; the existential clause
is the theorem conclusion.

The proof is `sorry` as required for a stage-2 statement. No dependency
modules are imported because all dependency notions are represented by Mathlib
classes (`CommRing`, `IsLocalRing`, `IsNoetherianRing`, `Module.Finite`, and
`Module.Flat`).

Edge cases checked: the index type is explicitly nonempty; directedness allows
cofinal upper stages; zero modules are admitted by `Module.Finite`; the flat
conclusion is meaningful for zero modules and for arbitrary characteristics.

Searches made: `rg` over `lean/Sheaf` and `WeilConjectures/` for eventual-flat and
colimit-flat declarations (no exact statement); Mathlib search for `Module.Flat`,
`Module.Finite`, `IsLocalRing`, and `IsNoetherianRing` (all matched existing
classes); `msearch.py` LeanFinder/Loogle queries for a theorem descending
flatness along filtered colimits (no exact declaration). The node is therefore
new.

## Earlier second reading (a previous round; superseded)

The declaration and node were reread together. The structure fields correspond to the stated stage hypotheses, and the theorem conclusion selects an index whose module is flat over its corresponding A-stage. No mismatch was found.

## Second reading by H1

I opened the node and module together, all four statement-dependency node
records, and the declarations they name. I read the Stacks source in the local
copy `/home/ubuntu/c1-stacks-review/algebra.tex`: the complete statements and
proofs of lemma-limit-module-essentially-finite-presentation (00QX),
lemma-colimit-eventually-flat (00R6), and
lemma-another-variant-local-criterion-flatness (00MO). The repository's
literature directory does not contain algebra.tex on this machine. The node
explicitly generalizes 00QX's finite-type hypotheses to Noetherian stages and
prime localization to arbitrary localization, as justified by 00MO and the
00R6 proof. This does not require a node correction.

The original Worker report and the earlier reading describe the original file;
the following independent reading supersedes their acceptance of that file.
The original structure had arbitrary proposition-valued fields, without either
the actual predicates or proofs of them. In particular `colimitFlat : Prop`
asserted no flatness. There were no limit objects or coprojections at all.
Its stage class fields were not installed as instances for subsequent fields,
and its theorem docstring was an ordinary comment. The module docstring and
step-by-step proof were missing. The signature record also flattened the source
rather than recording it verbatim. I replaced the unusable structure and its
theorem signature; I did not change the mathematical node statement.

Objects, hypotheses and conclusion, enumerated independently from the node:

1. A nonempty directed index set: `{Λ : Type u} [Preorder Λ] [Nonempty Λ]`
   and `hdir : ∀ i j, ∃ k, i ≤ k ∧ j ≤ k`. Verdict: exact; its thin category
   has an arrow precisely for a comparison, so the maps below are precisely
   the transition maps in the statement.
2. Stage commutative rings A_i and B_i: functors `A` and `B` into
   `CommRingCat.{v}` and `CommRingCat.{w}`. Verdict: exact, with ring structures
   supplied by the bundled objects, no field hypothesis or characteristic.
3. Noetherian local stage rings: the four dependent instance binders
   `[∀ i, IsLocalRing (A.obj i)]`, its B analogue, and their
   `IsNoetherianRing` analogues. Verdict: exact. The recorded dependency
   `IsNoetherianRing` is `IsNoetherian R R`; every ideal is finitely generated.
4. Finite B_i-modules N_i: `N : Λ ⥤ AddCommGrpCat.{z}` with dependent
   `Module (B.obj i) (N.obj i)` and `Module.Finite` instances. Verdict: exact.
   Mathlib's Module.Finite is finite generation of the top submodule, as the
   dependency node says; no finiteness of the ring or underlying set is assumed.
5. Local structure maps A_i -> B_i: `φ` and `hφ`. Verdict: exact.
   `IsLocalHom` reflects units; for local rings this is equivalent to mapping
   maximal ideal into maximal ideal (`IsLocalRing.local_hom_TFAE`, read in
   Mathlib/RingTheory/LocalRing/RingHom/Basic.lean).
6. Local A and B transition maps: `(A.map f).hom`, `(B.map f).hom`, `hA`, `hB`.
   Verdict: exact. Functor laws impose identity and composition, including
   the maps at equal indices, without additional assumptions.
7. Commuting structure-map squares: `hcomm` is equality of the two composites
   as ring homomorphisms. Verdict: exact.
8. Additive module transition maps and semilinearity:
   `(N.map f).hom` and `hscalar` spell out eta(b x) = beta(b) eta(x).
   Verdict: exact; N's functor laws impose identities and composition too.
9. Colimit rings A and B with coprojections: `cA : Cocone A`, `cB : Cocone B`,
   `hcA : IsColimit cA`, `hcB : IsColimit cB`. Verdict: exact universal
   properties in commutative rings. These are the Cocone and IsColimit
   declarations recorded by def-weil-pbc-category-colimit, not a private copy.
10. The induced ring map A -> B: `ψ` and `hψ` identify its composites with
    every A coprojection with φ followed by the B coprojection. Verdict: exact;
    the colimit universal property makes this precisely the induced map.
11. Colimit abelian group N and its induced B-module:
    `cN`, `hcN`, `[Module cB.pt cN.pt]`, and `hlimitScalar`. Verdict: exact.
    The equation ties the action to coprojections of the same stage. Directed
    colimits let any scalar and element be represented at a common stage, so
    this forces the entire action described by the node. The A action is
    restriction through ψ, not an unrelated supplied module structure.
12. Hypothesis (a), for every comparison i -> j: `hloc` installs the
    A_i-algebras from φ_i and the A transition map, then requires a ring map
    `q : B_i ⊗[A_i] A_j ->+* B_j` with its exact pure-tensor formula and a
    multiplicative subset `W` for which `IsLocalization W B_j` holds under
    q.toAlgebra. Verdict: exact. The pure tensors determine q uniquely, and
    commutativity supplies this canonical map. Mathlib's IsLocalization is
    the localization-map predicate (units, fraction representation, eventual
    equality), equivalent over rings to the node's kernel formulation.
13. Hypothesis (b), for every comparison: `hbase` requires a B_j-linear
    equivalence `B_j ⊗[B_i] N_i ≃ₗ[B_j] N_j` satisfying b tensor x -> b eta(x).
    Verdict: exact. Tensor symmetry exchanges the factors with the node's
    N_i tensor B_j; its specified map is an isomorphism iff this one is.
14. Flatness of N over the limit A: `hflat` is `Module.Flat cA.pt cN.pt`
    under `Module.compHom cN.pt ψ`. Verdict: exact. Module.Flat is the
    recorded flat-module notion, equivalent to preserving injectivity of all
    linear maps on tensoring (Flat/Basic.lean, inspected).
15. Conclusion: `∃ i : Λ, Module.Flat (A.obj i) (N.obj i)` under
    `Module.compHom (N.obj i) (φ i)`. Verdict: precisely the existential
    flat stage, over its first ring through its own structure map. No eventual
    forall, flatness of B_i, or extra finiteness is claimed.

Edge cases: empty indices are excluded by the node itself and by Nonempty,
not by an accidental type restriction. Zero stage/limit modules are allowed;
finite generation may have zero generators. Local rings are nontrivial in
Mathlib, matching the maximal-ideal convention in Stacks; the zero ring is
therefore excluded only at the local stages, as the node requires. There are
no schemes, dimensions, n, characteristic restrictions or field assumptions.
The index, first-ring, second-ring and additive-module universes are separately
bound by u, v, w, z. Arbitrary colimit objects can be supplied as cocones; no
HasColimits or universe-smallness hypothesis is imposed. All parameters and
universes are explicitly bound.

Independent searches (2026-10-11): msearch.py LeanSearch with the query
"finite modules over local rings in a directed system with localized base
change become flat at a stage if their limit is flat" was unavailable (HTTP
Internal Server Error), so no absence claim is based on it. LeanFinder query
"A finite module over a filtered system of Noetherian local rings is flat at
some stage when its direct limit is flat" returned adic-completion flatness,
smooth-algebra flatness, faithful flatness, and localization criteria; opening
the returned types shows none is this statement. Loogle
`Module.Flat, CategoryTheory.Limits.IsColimit` returned no hits (the earlier
unqualified IsColimit query was rejected and was not used as evidence).
msearch grep `flat.*(colimit|directLimit)|(colimit|directLimit).*flat` under
Mathlib/RingTheory returned no hits. Independent rg with those other names
(case-insensitive) on WeilConjectures and lean/Sheaf found preservation of
flat/K-flat objects under colimits, and the project's affine descent theorem
which cites this node; neither gives descent of flatness to one stage.
The new signature uses Mathlib's existing notions exclusively. No new
notion node or dependency module is needed; the private data structure has
been removed, not replaced by another definition.

Conventions and remaining obligations: one theorem, whose only proof is sorry;
no definitions or instances with hidden obligations. Both module and theorem
docstrings cite the source and blueprint id; the theorem docstring carries
all seven proof steps and their named dependencies. Lines are at most 100
characters. The node's lean.statement is copied verbatim from `theorem` up to
`:=` in the module. Server compilation and delivery preflight are run below.

Validation: scompile.py compiled the repaired module cleanly (exit 0, no
warnings). deliver2.py --no-push printed OK: the complete delivery passes
preflight and compiles. The cocone action uses explicit SMul.smul types to
avoid typeclass synthesis getting stuck on the definitionally equal constant
functor objects; this has no effect on the stated scalar-compatibility equation.
