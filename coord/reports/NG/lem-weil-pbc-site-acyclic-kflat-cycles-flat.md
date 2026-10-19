## Worker report

The module `Sheaf.Algebra.Homology.AcyclicKFlatCyclesFlat` states
`CochainComplex.isFlat_cycles_of_acyclic_isKFlat`, with proof `sorry`.
It makes no definitions and changes only the item's `lean` field.

Hypothesis and conclusion correspondence:

- A small site is `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C}`.
  This is the usual small-site universe convention of the recorded flat-sheaf
  interface; `u` is arbitrary, so there is no fixed cardinal bound on the site.
- The sheaf of commutative rings is `{R : Sheaf J CommRingCat.{u}}`.
  `sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})` forgets only commutativity
  when providing the ring sheaf argument of `SheafOfModules`.
- The cochain complex is `A : CochainComplex (SheafOfModules …) ℤ`.
- Acyclicity is the hypothesis `hA : A.Acyclic`, using Mathlib's exactness in every degree.
- K-flatness is `hK : A.IsKFlat`, exactly the recorded total-tensor predicate.
- Flat terms are `hflat : ∀ i : ℤ, SheafOfModules.IsFlat (R := R) (A.X i)`.
- Every integer degree is the unrestricted binder `(n : ℤ)`.
- Flatness of the cycle sheaf is `SheafOfModules.IsFlat (R := R) (A.cycles n)`.
  Mathlib's `HomologicalComplex.cycles` is the cycles of `A.sc n`, with its kernel
  inclusion `iCycles`; `cyclesIsKernel` identifies it as the kernel of the outgoing
  differential. In `ComplexShape.up ℤ`, that differential is `A.d n (n + 1)`.
  This is the categorical sheaf kernel, not the kernel of global sections.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.Acyclic`, `HomologicalComplex.cycles`, `cyclesIsKernel`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: `SheafOfModules.IsFlat`.
- Proof-only import `Sheaf.Algebra.Homology.AcyclicKFlatTensor` supplies
  `SheafOfModules.tensor_acyclic_of_isKFlat`.
- The tensor-complex proof dependency is already imported through KFlat:
  `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`.
- `lem-weil-pbc-site-flat-opcycles-tor-criterion` has no recorded declaration yet;
  it is used only in the natural-language proof, and its import is left for landing.
  It is not needed to state this result and is not a statement prerequisite.

The module and theorem docstrings cite Stacks Tag 0G7C. Read the source at
`literature/stacks-project/sites-cohomology.tex`, lemma-K-flat-flat-acyclic.
It assumes exactly K-flatness, acyclicity and flat terms. Its flat-resolution/Tor
argument confirms the conclusion; the theorem docstring gives all three steps
of the node's existing universal-tensor/opcycles proof route.

Edge cases: n = 0 and negative n remain included, since the indexing is ℤ with no
bound. The zero complex and zero ring are allowed and have zero, hence flat,
cycles. The empty site is allowed; no object, point or nonempty covering is
chosen. No boundedness, enough-points, nonzero or purity hypothesis is added.
The acyclicity hypothesis is essential to the stated argument and is retained.

Searches for an existing statement:

- msearch LeanFinder, "Cycles of an acyclic K-flat complex of flat sheaf modules
  are flat": eight ordinary-module flat tensor exactness results, no site-complex
  cycle-flatness theorem.
- msearch Loogle, "IsKFlat, cycles": no hits, unknown identifier IsKFlat.
- msearch LeanSearch, "Cycles of an acyclic K-flat complex of flat sheaves of
  modules are flat": service unavailable (Internal Server Error).
- msearch Mathlib grep, `cycles.*[Ff]lat|[Ff]lat.*cycles`: zero hits.
- rg with the same regex in upstream WeilConjectures and project lean/Sheaf:
  ordinary-module and affine-scheme opcycles criteria and unrelated tensor-cycle
  lemmas; none is this arbitrary small-site assertion.
- The same upstream/project search included the exact item id; no declaration.
  The source signatures and docstrings of the recorded dependencies were opened;
  the current server source for Flat was also read with scompile --source and
  agrees with the local recorded module.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag.
All theorem proofs are postponed, and all variables and universes are explicit.

## Second reading by NG

Independently read the node, the delivered module, all four statement-dependency
records and declarations, the tensor-complex and universal-tensor proof interfaces,
and Stacks sites-cohomology.tex, Flat resolutions, especially Tag 0G7C
(lines 3384–3415). The section assumes ringed sites, with no boundedness,
nonemptiness, points, or finiteness convention. Also read the ringed-site and
flat-module definitions in sites-modules.tex and K-flat Definition 06YN.

Object/hypothesis/conclusion checklist:

- Small site C with topology: `{C : Type u} [Category.{u} C]`
  and `{J : GrothendieckTopology C}`. Pass: arbitrary small category and topology;
  no chosen object or restricted topology. This uses the small-site size
  convention of the recorded flat-sheaf interface, with arbitrary universe u.
- Sheaf of commutative rings O: `{R : Sheaf J CommRingCat.{u}}`. Pass:
  commutative rings, including the zero ring; no field or characteristic instance.
  The displayed `sheafCompose` forgets commutativity solely to give the canonical
  ring-sheaf input to `SheafOfModules`, retaining the same ring and modules.
- Cochain complex of module sheaves: `A : CochainComplex (SheafOfModules ...)
  ℤ`. Pass: the recorded Mathlib cochain-complex declaration specializes to
  `ComplexShape.up ℤ`, so differentials go from i to i+1 and square to zero.
- Acyclicity: `(hA : A.Acyclic)`. Pass: opened Mathlib's declaration
  `HomologicalComplex.Acyclic := ∀ i, K.ExactAt i` and its homology-vanishing
  equivalence. This is exactness of sheaves, not of sections.
- K-flatness: `(hK : A.IsKFlat)`. Pass: the recorded KFlat module defines
  acyclicity of the direct-sum total tensor with every acyclic complex.
  Its generalized site-universe interface specializes here without an extra
  instance or a change of predicate.
- All terms flat: `(hflat : ∀ i : ℤ,
  SheafOfModules.IsFlat (R := R) (A.X i))`. Pass: the recorded IsFlat definition
  is exactness of `tensorRight`, using the sheaf tensor product, exactly as
  Definition 03ER(3). Its sheafification infrastructure is synthesized, not an
  additional theorem hypothesis.
- Every integer n: `(n : ℤ)` after all the hypotheses. Pass: no lower or upper
  bound; quantification gives the asserted conclusion separately at every degree.
- Cycle sheaf equals the kernel of d^n, and is flat:
  `SheafOfModules.IsFlat (R := R) (A.cycles n)`. Pass: opened the definition
  of cycles and `HomologicalComplex.cyclesIsKernel`; they give the kernel of
  the outgoing differential `A.d n (n+1)` in the sheaf-module category.
  No conclusion was added or omitted.

Edge cases: n=0 and negative n use the same ℤ indexing; zero complexes, zero rings,
and empty sites are permitted, and no index family or covering is assumed
nonempty. There is no scheme hypothesis, so the empty scheme supplies no special
restriction. All characteristics are included. Universes are explicitly bound;
no test-object quantification in a smaller independent universe occurs. The
signature uses the dependency's small-site/ring/module universe convention,
not the unequal-universe small pro-etale interface of a different node.

Independent duplicate searches (different queries from the first reader):

- LeanFinder via msearch: "Flatness of kernels in a tensor exact acyclic complex
  of flat module sheaves". Eight ordinary Module.Flat tensor-exactness results;
  none states this cycle-sheaf assertion.
- Loogle via msearch: `"cycles", "flat"`. No results.
- LeanSearch via msearch: "The kernel of a differential of an acyclic K-flat
  complex with flat terms is flat". Service unavailable (Internal Server Error),
  recorded as unavailable, not as a negative result.
- rg over upstream WeilConjectures, project lean/Sheaf, Mathlib homological
  algebra and flat-module files, for flat/kernel/cycles in both orders and the
  exact declaration name. Related hits are ordinary-module flat opcycles,
  affine sheaf opcycles, and general `ObjectProperty.flat_opcycles_of_exactAt`.
  Opened the latter in upstream DerivedCategory/FlatModel.lean: its conclusion
  concerns opcycles, with different hypotheses; it is not this theorem.
  The exact item/declaration also has no upstream-name-table match.

No mismatch found; no Lean or node correction made, and no new definition or
repaired dependency is needed. In particular no stronger purity hypothesis is
introduced. The theorem docstring reproduces each of the node's three proof
steps: universal tensor acyclicity in degree n-2, flat opcycles in degree n-1,
and the acyclic cokernel-to-cycle isomorphism. The unavailable opcycle theorem
is only a proof dependency and does not prevent stating this theorem. No new
definition or proved theorem occurs; the sole proof is `sorry`. Source and
blueprint docstrings, namespace, imports, and 100-character lines pass.

Verification: scompile.py compiled the sole delivered module cleanly on the
server (nice 19, two threads, 60-second per-file limit; 1.3 seconds). The node's
lean.statement was checked verbatim against the complete declaration signature;
all variables/universes are bound and no file-local statement notation is used.
