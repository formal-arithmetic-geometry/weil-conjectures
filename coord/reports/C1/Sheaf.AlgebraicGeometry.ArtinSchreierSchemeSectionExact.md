## What changed

Proved `AlgebraicGeometry.Scheme.artinSchreier_section_data_shortExact` without
changing its signature. The proof constructs a singleton surjective étale covering
for every section, proves that its generator belongs to the image sieve using
`hwp`, `hrestr`, and the inverse section equivalence, and obtains epimorphy.
It then applies a separate kernel-identification obligation and derives exactness
and monomorphy using the categorical kernel API before constructing `ShortExact`.

Added two modules and their nodes. `ArtinSchreierPolynomialCover` is fully proved:
it constructs the standard étale pair `(T^p-T-t,1)`, explicitly identifies its
algebra with the monic root algebra, proves faithful flatness, and pulls its
spectrum and root back along `U.toSpecΓ`. `ArtinSchreierSectionKernel` states only
the left two exactness assertions, as a limiting kernel fork; it does not claim
surjectivity of `wp`. The parent's node now records this actual proof.

## Proved and sorry left

Proved the item's sole sorry:
`AlgebraicGeometry.Scheme.artinSchreier_section_data_shortExact`.
Also proved `AlgebraicGeometry.Scheme.exists_etale_surjective_artinSchreier_eq_appTop`,
node `lem-sc-artin-schreier-polynomial-cover`, without any sorry.

This is a decomposition: one original hole is closed and one new hole is added;
the net hole reduction is zero. The polynomial-cover lemma itself is fully proved.

One new named sorry remains:
`AlgebraicGeometry.Scheme.artinSchreier_section_data_isKernel`, node
`lem-sc-artin-schreier-section-kernel`. Its exact theorem body is `:= by sorry`
and its docstring gives the full stalk comparison, root identification, and
conservativity argument. Its conclusion is strictly part of the original theorem:
it contains no epimorphy assertion and the right-surjectivity proof is actual Lean.

All three modules compiled cleanly together with `lcompile.py --all`.

## No longer needed

Removed the parent's direct proof imports:
- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`;
- `Sheaf.RingTheory.LocalRing.ArtinSchreierKernel`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier`.

The first three remain used by the kernel obligation. The last is not used by
the polynomial-cover proof: faithful flatness gives surjectivity directly,
so `lem-weil-pbc-surjective-nonempty-fibres` is no longer needed by this route.
`lem-weil-pbc-open-immersion-etale` is also unnecessary: the construction uses one
pullback over the spectrum of global functions instead of affine-open covers.
Their modules may remain transitively imported by existing public dependencies;
this is not a claim that they are globally unreachable. The parent's former direct
stalk dependencies are now used inside the kernel node. No unit statement or step
is removed; `sk-prop-cd.realized` has no entries for this item.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's affine-open covering step can be simplified:
the construction already used for Kummer in the source library pulls a single
polynomial cover back along `U.toSpecΓ`; this works on arbitrary schemes. The
curve exactness theorem is unusable here because it has extra field and curve
hypotheses. Searches found generic standard-étale and categorical kernel APIs,
not a duplicate general-scheme Artin--Schreier theorem. LeanSearch returned HTTP 500
and is recorded as unavailable, not as evidence that no theorem exists.

The source citations have a distinction: Tag 03PL is the Kummer polynomial-cover
proof; Tag 0A3J asserts the Artin--Schreier sequence. The new polynomial lemma
adapts the former argument with derivative `-1`, rather than claiming 03PL states
Artin--Schreier exactness. Both source pages were read.

Edge cases: the polynomial theorem treats a zero global section ring separately
using the identity and zero function. For nonzero rings, primality gives p>1,
which ensures the leading term survives and its degree is positive. The main
site proof permits empty schemes and works with the given universe lift; its
kernel obligation includes the empty conservative family. No nonemptiness,
connectedness, affine, or curve hypothesis was added. The kernel claim is valid
for disconnected schemes because constant sheaves allow locally constant sections.

## New nodes

`lem-sc-artin-schreier-polynomial-cover` records the fully proved construction of
a surjective étale cover solving a single equation over an arbitrary scheme.
Its module is `Sheaf.AlgebraicGeometry.ArtinSchreierPolynomialCover`. The explicit
standard-étale root equivalence and faithful-flatness argument realize the
polynomial-cover part of the source proof.

`lem-sc-artin-schreier-section-kernel` records the remaining kernel identification
for the specified maps and section formulas. Its module is
`Sheaf.AlgebraicGeometry.ArtinSchreierSectionKernel`. It uses the existing
constant-sheaf stalk, local-ring kernel, stalk exactness and conservativity nodes.
Both nodes have complete self-contained statements and recorded real searches.
The existing item's nearest blueprint ancestor command returned `None`; their
blueprint origin therefore records null with the two created ancestor nodes in
`via`. Searches across all blueprint chapters found the finite-field affine-line
cover and curve sequence, which do not state these general-scheme lemmas.


## Second reading by C1

1. Compared the item against the repository with diff. Its sole existing theorem's
   signature and docstring are byte-for-byte unchanged. There are no changed definitions
   or change records. The new modules introduce only their recorded theorems.
2. All three files compile with lcompile.py in import order. Scratch #print axioms checks
   show only propext, Classical.choice and Quot.sound for the polynomial-cover theorem;
   the kernel obligation and parent additionally use sorryAx. There is exactly one
   explicit sorry, in artinSchreier_section_data_isKernel. No forbidden declaration or
   hollow definition exists. The main theorem is conditional on that remaining hole.
3. Read both new statements, docstrings and nodes. The kernel assertion is strictly the
   left two exactness assertions, not the whole target: it does not imply Epi wp. Local
   surjectivity is independently proved. The kernel claim works for disconnected schemes
   (locally constant sections) and the empty scheme. The polynomial proof handles the
   zero ring separately; for p=2 its degree comparison and derivative -1 still hold.
   The standard-etale equivalence, positive-degree faithful flatness and pullback equation
   are actual checked Lean, not extra obligations. Read Stacks Tags 0A3J and 03PL; the
   latter supplies the adjoining-root method, not the Artin-Schreier statement itself.
   Fresh LeanFinder and Loogle searches used locally constant roots and KernelFork API
   terminology, and rg covered the existing ArtinSchreier modules. An existing theorem
   AlgebraicGeometry.artinSchreier_kernel_sections needs only a map to Spec of a field,
   not a curve. hp gives such a map to Spec (ULift (ZMod p)); this could close the new
   kernel obligation using its existing sectionwise hole. However that module has no
   compiled object in the last green library, so the project rule forbids using it yet.
   The attempted reduction was removed; no duplicate of that declaration was added.
4. Checked the full old proof_deps against the new parent and both child nodes. The old
   constant-sheaf, scheme, standard-etale, geometric-point, stalk, local-ring and
   conservativity entries are now statement prerequisites or children dependencies.
   The surjective-nonempty-fibres and open-immersion-etale nodes are genuinely unused
   by this route. No realized unit node is bypassed: sk-prop-cd.realized has no entries
   for this item. Retained the shortest currently compilable route. Parent proof imports
   are private. Replaced the new kernel module's public ShortExact import with the narrower
   public Kernels import, which supplies its signature's KernelFork and IsLimit.
5. Checked each node's lean.statement against the theorem signature, proof steps against
   the body (or complete docstring for the hole), and proof_deps against the union of
   step uses. New nodes have source, searches, created, blueprint, chapter/unit and lean
   records. The parent records the actual singleton-cover/image-sieve argument and kernel
   packaging; the polynomial node records the proved standard-etale construction.

Second reading changed the kernel module's public categorical import, corrected the
report to count this as a decomposition with net zero holes, and documented the available
but not yet compiled sectionwise reduction. No existing statement or definition changed.
