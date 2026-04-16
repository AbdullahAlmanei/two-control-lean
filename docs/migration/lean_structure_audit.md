# Lean Structure Audit

This note separates the current Lean declarations into three different roles:

1. quantum-language interface:
   declarations that translate Mathlib matrices, vectors, Kronecker products, and predicates into the vocabulary of qubits, gates, and controls.
2. reusable proof infrastructure:
   declarations that are not paper steps themselves, but repeatedly solve indexing, block-matrix, unitarity, conjugation, and transport problems.
3. actual proof steps:
   declarations whose main purpose is to prove a numbered lemma/theorem from Sections 3-7, or a local one-off step tightly coupled to one of those proofs.

The main architectural issue in the current tree is that many reusable proof-infrastructure lemmas are private and redefined inside later section files. That makes the section files look larger than the paper structure, and it blurs the distinction between vocabulary and proof.

## Classification rule

Use this rule when deciding where a declaration belongs.

- If it changes notation, indexing, or presentation from Mathlib into quantum language, it is interface.
- If it is reused across sections and does not correspond to a paper statement, it is reusable proof infrastructure.
- If it exists only to advance one numbered section lemma or theorem, it is a proof step.

Corollary:

- Public declarations with paper numbering should stay in section files.
- Shared helper declarations should not live in section files once they are used in two or more sections.
- Private declarations are not automatically proof steps. Many current private declarations are really shared infrastructure that only stayed private because they were copied forward.

## Current File Roles

### `Prelude.lean`

Interface:

- `Mat`, `Square`, `Vec`
- `†`
- `kron`, `⊗ₖ`

Target home:

- Keep exactly as the foundation layer.

### `Definitions.lean`

Interface and quantum vocabulary:

- `diag2`, `diag4`
- `ket0`, `ket1`
- `ketbra`, `proj0`, `proj1`
- `kronVec`
- `controlledGate`, `ccu`
- `abgate`, `bcgate`, `acgate`
- `swap2`, `swapab`, `swapbc`
- `IsProductState`, `IsEntangled`, `IsQubit`
- `TwoQubitGate`
- `inCanonicalPair`

Target home:

- Keep exactly as the quantum vocabulary layer.

### `BlockHelpers.lean`

Interface and reusable proof infrastructure:

- Kronecker access and transport: `kron_apply`, `kron_add_left`, `kron_smul_left`, `zero_kron_left`, `zero_kron_right`, `one_kron_one`
- First-qubit matrix units: `proj01`, `proj10`
- Reindexing and block syntax: `finTwoProdSumEquiv`, `finTwoBlockEquiv`, `BlockMatrix`, `blockAlgEquiv`, `blockify`, `unblockify`
- Block transport lemmas: `blockify_injective`, `blockify_mem_unitaryGroup_iff`, `blockify_proj0_kron`, `blockify_proj01_kron`, `blockify_proj10_kron`, `blockify_proj1_kron`, `blockify_blockExpansion`, `unblockify_fromBlocks`, `blockDecomposition`
- Diagonal/block bridge: `diag2_decomp`, `blockify_diag2_kron_one`

Target home:

- Keep as a shared helper layer.
- Expand it with the repeated indexing and block lemmas now duplicated in later sections.

### `DiagonalizationHelpers.lean`

Reusable proof infrastructure:

- Diagonal/unitary facts: `diag2_one_one`, `diag2_unitary`, `diag2_kron_diag2`, `controlledGate_diag2_eq`
- Unitary transport: `unitary_conj_mem_unitaryGroup`, `conjTranspose_mem_unitaryGroup`
- Spectral decomposition core: `unitary_diag2_exists`
- Kronecker/unitary transport: `kron_mul_two`, `conjTranspose_kron_two`, `kron_unitary_two`
- Characteristic polynomial facts: `charpoly_unitary_conj`, `roots_charpoly_diag4`

Target home:

- Keep as the spectral and unitary helper layer.
- Make it the canonical home for `diag4_unitary` and similar repeated unitarity lemmas when they are extracted from section files.

### `Section3.lean`

Actual proof steps:

- `section3_lemma_3_1`
- `section3_lemma_3_2`
- `section3_lemma_3_3`

Reusable proof infrastructure currently embedded here:

- Indexing and Kronecker: `finProd_assoc_222`, `kron_one_assoc`, `kron_smul_right`
- Block/unitary transport: `block_one_eq`, `block_diagonal_unitary`, `fromBlocks_diagonal_unitary`
- Diagonal/unitary transport: `diag2_same_eq_smul_one`, `diag4_unitary`, `diag4_repeat_norms_of_mem_unitaryGroup`, `one_kron_diag2`
- SWAP and gate conjugation: `swap2_conjTranspose`, `swap2_mul_swap2`, `swap2_unitary`, `swap2_conj_diag4`

Local proof-step support that can stay private:

- `blockify_W`, `block_scalar_eq`, `smul_eq_smul_implies_zero`
- `tensor_witness_of_eq`, `tensor_witness_of_mul_eq_one`, `eq_or_mul_eq_one_of_three_multiset`
- `one_kron_mul_controlledGate_diag2`, `blockify_diag4`, `repeated_pair_complement`
- `notc`, `notc_conjTranspose`, `notc_mul_notc`, `notc_unitary`, `notc_conj_diag4`
- `cnot`, `cnot_conjTranspose`, `cnot_mul_cnot`, `cnot_unitary`, `cnot_conj_diag4`

### `Section4.lean`

Actual proof steps:

- `section4_lemma_4_1`
- `section4_lemma_4_2`
- `section4_lemma_4_3`
- `section4_lemma_4_4`

Reusable proof infrastructure currently embedded here:

- Column and projector transport: `unitary_column0_norm`, `unitary_column1_norm`, `unitary_columns_orthogonal_left`, `unitary_columns_orthogonal_right`, `unitary_column_projector_sum`
- Ketbra/mulVec bridge: `ketbra_mulVec`, `ketbra_self_mulVec_of_dotProduct_eq_one`, `ketbra_orthogonal_mulVec`, `ketbra_eq_proj1_of_first_zero`, `ketbra_eq_proj0_of_second_zero`
- Indexing and Kronecker: `finProd_assoc_222`, `kron_add_right`, `kron_mul_reindex_local`, `kron_assoc_222_local`, `split_one_kron_terms`
- Block and unitarity transport: `block_one_eq`, `fromBlocks_diagonal_unitary`, `block_diagonal_unitary`, `diag4_unitary`, `diag4_repeat_norms_of_mem_unitaryGroup`, `one_kron_diag2`, `mul_eq_zero_of_unitary_left`, `mul_eq_zero_of_unitary_right`, `eq_zero_of_one_kron_eq_zero`
- Gate embedding and conjugation: `swap_index_prod`, `swap2_left_mul_apply`, `swap2_right_mul_apply`, `swap2_conj_apply`, `swap2_mul_swap2_aux`, `swap2_conj_kron_right_local`, `swap2_conj_kron_left_local`, `swap2_conj_kron_local`, `bcgate_kron_two`, `acgate_kron_two`, `swapab_conj_bcgate_kron_two`, `swapab_conj_acgate_kron_two`, `blockify_bcgate`, `blockify_acgate`, `controlledGate_unitary`, `swap2_conjTranspose_local`, `swap2_mul_swap2_local`, `kron_mul_reindex`, `conjTranspose_kron_reindex`, `swapab_mul_swapab`, `swapbc_conjTranspose`, `swapab_conj_acgate`, `swapab_conj_bcgate`, `ccu_diag2_conjTranspose`

Local proof-step support that can stay private:

- `diag4_one`, `proj0_add_proj1`, `controlledGate_diag2_one`, `ccu_diag2_one`
- `finProd_assoc_11`, `ccu_diag2_last_zero_block`, `ccu_diag2_last_one_block`, `ccu_diag2_11_block`
- `swapab_conj_word_acbc`, `swapab_conj_word_bcac`, `swapab_conj_ccu_diag2`

### `Section5.lean`

Actual proof step:

- `section5_lemma_5_1`

Reusable proof infrastructure currently embedded here:

- Repeated indexing, Kronecker, block, and swap families from Sections 3-4: `finProd_assoc_222`, `kron_one_assoc`, `proj0_add_proj1`, `block_one_eq`, `kron_add_right`, `kron_smul_right`, `kron_mul_reindex_local`, `kron_assoc_222_local`, `swap_index_prod`, `swap2_left_mul_apply`, `swap2_right_mul_apply`, `swap2_conj_apply`, `swap2_conj_kron_right_local`, `acgate_kron_two`, `blockify_bcgate`, `blockify_acgate`, `blockify_abgate`, `blockify_controlledGate`, `mul_eq_zero_of_unitary_left`, `mul_eq_zero_of_unitary_right`, `block_diagonal_unitary`, `fromBlocks_diagonal_unitary`, `controlledGate_unitary`, `diag2_one_right_kron`, `notc`, `notc_conjTranspose`, `notc_mul_notc`, `notc_unitary`, `diag4_unitary`, `notc_conj_diag4`

Local proof-step support that can stay private:

- `nonzero_of_unitary`, `exists_nonzero_entry_of_ne_zero`, `eq_zero_of_kron_right_entry_ne_zero`
- `scalar_of_kron_sum_zero`, `tensor_decomp_of_offdiag_zero`, `unitary_factors_of_kron_unitary`
- `unit_vector_extends_to_unitary`, `eq_witness_of_eq`, `prod_one_witness`

### `Section6.lean`

Actual proof steps:

- `section6_lemma_6_1`
- `section6_lemma_6_2`
- `section6_lemma_6_3`
- `section6_lemma_6_4`

Interface-like state vocabulary and reusable state infrastructure:

- New state vocabulary: `ketPlus`, `qubitPerp`, `colMatrix`, `detVec2`, `detVec4`
- Qubit and product-state transport: `isQubit_iff_star_dot_eq_one`, `isQubit_ket0`, `isQubit_ket1`, `isQubit_ketPlus`, `isQubit_ne_zero`, `isQubit_mulVec_of_unitary`, `isQubit_of_kron_right`, `isQubit_of_kron_left`, `isQubit_kron`, `isQubit_qubitPerp`
- Product-state and entanglement transport: `detVec4_smul`, `detVec4_kronVec`, `detVec4_add_kronVec`, `detVec4_add_smul`, `isProductState_of_detVec4_eq_zero`, `detVec4_eq_zero_of_isProductState`, `isProductState_iff_detVec4_eq_zero`, `isEntangled_iff_detVec4_ne_zero`, `isProductState_smul`, `qubit_product_state_factors`
- Vector and normalization transport: `vec2_basis_decomp`, `vec4_basis_decomp`, `sumSq_ne_zero_of_ne_zero`, `normalize_vec2`, `exists_smul_of_detVec2_eq_zero`, `quadratic_root_eq_zero`
- Kronecker/vector transport: the `kronVec_*` application lemmas, `dot_kronVec_two_two`, `dot_kronVec_two_two_cross`, `kronVec_comp_finProdFinEquiv_eq_vec`, `kron_mulVec_reindexed`, `kron_mulVec_two_two`, `kronVec_assoc_222`
- Matrix basis/unitary transport: `mulVec_ne_zero_of_unitary`, `colMatrix_mulVec`, `colMatrix_unitary_of_orthonormal`, `qubitPerp_orthogonal`, `qubit_basis_unitary`

Reusable gate infrastructure currently duplicated here:

- `finProd_assoc_222`, `proj0_add_proj1`, `kron_add_right`, `kron_mul_reindex_local`, `kron_assoc_222_local`
- `swap_index_prod`, `swap2_left_mul_apply`, `swap2_right_mul_apply`, `swap2_conj_apply`, `swap2_mul_swap2_local`, `swap2_conj_kron_right_local`, `swap2_conj_kron_left_local`, `swap2_mul_swap2_aux`, `swap2_mulVec_kronVec`, `swap2_conjTranspose_local`, `swap2_mem_unitaryGroup`, `swap2_conj_kron_local`
- `bcgate_kron_two`, `acgate_kron_two`, `kron_two_unitary`, `acgate_localA_eq`, `acgate_localC_eq`, `acgate_localA_commute_bcgate`, `unitary_fix_of_adj_fix`, `swapab_mul_swapab`, `swapab_mulVec_kronVec`, `swapbc_mul_swapbc`, `swapab_conj_bcgate_kron_two`, `swapab_conj_acgate_kron_two`, `swapab_conj_acgate`, `swapab_conj_bcgate`, `bcgate_localB_commute_acgate`, `swapbc_mulVec_kronVec`, `bcgate_mulVec_kronVec`, `acgate_mulVec_kronVec`, `acgate_mulVec_of_product`
- `block_one_eq`, `block_diagonal_unitary`, `upper_block_zero_of_unitary`, `blockify_acgate`

Local proof-step support that can stay private:

- `exists_product_state_on_left_ket0`
- `controlled_on_second_mulVec_ket0`, `acgate_fix_of_output_fix`, `swapbc_mulVec_vec4_ket0`
- `acgate_suffix_ket0`, `acgate_prefix_ket0`, `acgate_fixed_middle_eq`
- `dot_mulVec_of_unitary`, `colMatrix_conjTranspose_mulVec_left`, `colMatrix_conjTranspose_mulVec_right`
- `exists_unitary_of_fixed_right_factor`, `exists_unitary_of_fixed_left_factor`
- `controlled_on_first_of_fixing_basis`, `controlled_on_second_of_fixing_basis`, `controlled_on_first_of_two_images`, `zero_matrix_of_mulVec_pair_det_ne_zero`, `controlled_on_first_of_entangled_input`
- `section6_lemma_6_2_branchB`, `section6_lemma_6_2_caseC`, `section6_lemma_6_2_caseA`, `section6_lemma_6_3_normalize_V₂`, `section6_lemma_6_3_identity_transfer`
- `conjTranspose_kron_reindex_local`, `ccu_diag2_conjTranspose_local`, `controlledGate_mulVec_left_zero`, `ccu_mulVec_left_zero`, `ccu_mulVec_ket1_ket0`, `ccu_mulVec_middle_ket0`

### `Section7.lean`

Actual proof steps:

- `section7_lemma_7_1`
- `section7_lemma_7_2`
- `section7_lemma_7_3`
- `section7_theorem_7_4`
- `section7_corollary_7_5`

Reusable proof infrastructure currently embedded here:

- Diagonal and unitary transport: `diag4_unitary`, `one4_unitary`, `unitary_mul2`, `unitary_mul3`, `unitary_mul4`, `unitary_mul_swap2_right`, `unitary_mul_swap2_left`
- Repeated indexing and Kronecker: `finProd_assoc_222`, `kron_add_right`, `kron_mul_reindex_local`, `kron_assoc_222_local`, `proj0_add_proj1`, `split_one_kron_terms`
- Swap and conjugation families: `swap_index_prod`, `swap2_left_mul_apply`, `swap2_right_mul_apply`, `swap2_conj_apply`, `swap2_mul_swap2_local`, `swap2_conj_kron_right_local`, `swap2_conj_kron_left_local`, `swap2_conj_kron_local`, `swapab_conj_kron_three`, `swap2_conjTranspose_local`, `swap2_mul_swap2_aux`, `swap2_mem_unitaryGroup`, `swapab_mul_swapab`, `swapbc_mul_swapbc`, `swapac`, `swapac_mul_swapac`, `swapab_conj_abgate`, `swapbc_conj_ac`, `swapbc_conj_bcgate`, `swapab_conj_acgate`, `swapab_conj_bcgate`, `swapac_conj_ab`, `swapac_conj_ac`, `swapac_conj_bc`, `swapbc_conj_kron`, `swap2_conj_unitary`
- Gate transport and cancellation: `bcgate_kron_two`, `acgate_kron_two`, `swapab_conj_bcgate_kron_two`, `swapab_conj_acgate_kron_two`, `bcgate_localC_eq`, `abgate_commute_localC`, `acgate_localC_eq`, `localC_cancel_right`, `localC_cancel_left`, `bcgate_localC_cancel_right`, `bcgate_localC_cancel_left`, `bcgate_localC_conj_kron`, `controlledGate_conj_local_target`, `ccu_conj_local_target`, `conj_local_target_twoQubitGate`, `conj_local_target_product_four`
- Two-qubit gate transport: `swapab_twoQubitGate`, `swapac_twoQubitGate`

Local proof-step support that can stay private:

- `diag8`, `ccu_diag2_eq`, `abgate_controlledGate_diag2_eq`, `abgate_controlled_mul_ccu`, `section7_lemma_7_1_left`, `ccu_mul_abgate_controlled`, `section7_lemma_7_1_right`
- `swapbc_conj_mul2`, `swapbc_conj_ccu_diag2_one`, `swapac_conj_ccu_diag2_one`, `swap2_conj_diag4_one`
- `canonicalPair_first_norm`, `canonicalPair_step`
- `swapbc_conj_word_acab`, `normalize_word_acabac`, `normalize_word_acbcab`, `normalize_word_bcabac`, `swapbc_conj_word_abacbc`, `swapbc_conj_word_abacabbc`, `swapbc_conj_word_abbabbc`, `swapbc_conj_word_abbcacbc`, `section7_lemma_7_2_step3`
- `diag2_same_eq_smul_one_local`, `det_of_unitary_diag2_decomp_local`

## Duplicate Families That Should Move Out Of Section Files

Highest-priority duplicates:

- `finProd_assoc_222`
- `proj0_add_proj1`
- `kron_add_right`
- `kron_mul_reindex_local`
- `kron_assoc_222_local`
- `swap_index_prod`
- `swap2_left_mul_apply`
- `swap2_right_mul_apply`
- `swap2_conj_apply`
- `swap2_conjTranspose` or `swap2_conjTranspose_local`
- `swap2_mul_swap2` or `swap2_mul_swap2_local` or `swap2_mul_swap2_aux`
- `swap2_unitary` or `swap2_mem_unitaryGroup`
- `swap2_conj_kron_right_local`
- `swap2_conj_kron_left_local`
- `swap2_conj_kron_local`
- `bcgate_kron_two`
- `acgate_kron_two`
- `swapab_conj_bcgate_kron_two`
- `swapab_conj_acgate_kron_two`
- `block_diagonal_unitary`
- `fromBlocks_diagonal_unitary`
- `diag4_unitary`

Second-wave duplicates:

- `blockify_abgate`, `blockify_bcgate`, `blockify_acgate`
- `controlledGate_unitary`
- `kron_one_assoc`
- `one_kron_diag2` and `diag2_one_right_kron`
- `diag2_same_eq_smul_one`
- `conjTranspose_kron_reindex`
- SWAP-on-8-qubit conjugation and gate-word normalization helpers

These declarations are not paper statements. They are infrastructure. They should stop being defined in sections.

## Recommended Target Module Structure

Keep the proof import order, but freeze the helper-module structure before touching `Section3`.

```text
TwoControl/
   Prelude.lean
   Definitions.lean
   BlockHelpers.lean
   DiagonalizationHelpers.lean
   KronHelpers.lean
   SwapHelpers.lean
   GateHelpers.lean
   StateHelpers.lean
   Section3.lean
   Section4.lean
   Section5.lean
   Section6.lean
   Section7.lean
```

Recommended responsibilities:

- `Prelude.lean`: type aliases, notation, base imports.
- `Definitions.lean`: all quantum vocabulary and predicates.
- `BlockHelpers.lean`: reindexing, blockification, block decomposition, first-qubit matrix units, projector sums, fixed `Fin`-equivalence lemmas, generic block-unitary transport.
- `DiagonalizationHelpers.lean`: diagonal/unitary/spectral lemmas and diagonal-specific Kronecker specializations.
- `KronHelpers.lean`: associativity, multiplicativity, scalar/additivity transport, and cancellation lemmas for Kronecker products.
- `SwapHelpers.lean`: raw `swap2` and 3-qubit swap identities, conjugation formulas, and tensor transport by swap.
- `GateHelpers.lean`: `abgate`/`bcgate`/`acgate` transport, `controlledGate` transport, blockify lemmas for embedded gates, local-target cancellation, and `TwoQubitGate` transport.
- `StateHelpers.lean`: qubit-state, product-state, entanglement, vector normalization, and `mulVec` action lemmas that are not section-specific.
- `Section3.lean` to `Section7.lean`: only numbered results plus strictly local proof-step support.

## Refactor Policy

Do not work in abstract phases.

Instead:

1. decide the full helper-file layout before touching any section proof,
2. create those helper files with their final ownership boundaries up front,
3. when refactoring `Section3`, extract every `Section3` declaration that belongs in a helper file before moving to `Section4`,
4. repeat section by section.

The important constraint is that helper ownership is decided globally first, but the proof cleanup happens section by section.

## Helper Manifest To Freeze Before Starting Section Work

Before editing `Section3.lean`, create these helper files and commit to the following ownership plan.

### `BlockHelpers.lean`

Keep existing declarations. Planned additional owners:

- `finProd_assoc_222`
- `proj0_add_proj1`
- `block_one_eq`
- `block_diagonal_unitary`
- `fromBlocks_diagonal_unitary`
- `upper_block_zero_of_unitary`
- any shared `finProdFinEquiv_*` and `finProdFinEquiv_symm_*` index constants that are reused outside one section

Do not move theorem-specific indexing lemmas such as `finProd_assoc_11` here.

### `DiagonalizationHelpers.lean`

Keep existing declarations. Planned additional owners:

- `diag4_unitary`
- `diag4_repeat_norms_of_mem_unitaryGroup`
- `diag2_same_eq_smul_one`
- `one_kron_diag2`
- `diag2_one_right_kron`
- `det_diag2`
- `det_of_unitary_diag2_decomp`

Do not create new helper wrappers for trivial facts such as `one4_unitary`; use `Submonoid.one_mem _` where possible.

### `KronHelpers.lean`

Create this file before section work starts.

Initial imports:

- `import TwoControl.DiagonalizationHelpers`

Planned owners:

- `kron_add_right`
- `kron_smul_right`
- `kron_one_assoc`
- `kron_mul_reindex_local` with the `_local` suffix removed
- `kron_mul_reindex`
- `kron_assoc_222_local` with the `_local` suffix removed
- `split_one_kron_terms`
- `eq_zero_of_one_kron_eq_zero`
- `conjTranspose_kron_reindex`
- `conjTranspose_kron_reindex_local`

Do not duplicate `kron_unitary_two`; later sections should use the existing `kron_unitary_two` from `DiagonalizationHelpers.lean` whenever it is sufficient.

### `SwapHelpers.lean`

Create this file before section work starts.

Initial imports:

- `import TwoControl.KronHelpers`

Planned owners:

- `swap_index_prod`
- `swap2_left_mul_apply`
- `swap2_right_mul_apply`
- `swap2_conj_apply`
- `swap2_conjTranspose` as the canonical name
- `swap2_mul_swap2` as the canonical name
- `swap2_unitary` or `swap2_mem_unitaryGroup`, but only one canonical exported name
- `swap2_conj_diag4`
- `swap2_conj_kron_right_local` with the `_local` suffix removed
- `swap2_conj_kron_left_local` with the `_local` suffix removed
- `swap2_conj_kron_local` with the `_local` suffix removed
- `swap2_mulVec_kronVec`
- `swapab_mul_swapab`
- `swapbc_mul_swapbc`
- `swapac`
- `swapac_mul_swapac`
- raw swap/tensor conjugation lemmas such as `swapab_conj_kron_three` and `swapbc_conj_kron`

### `GateHelpers.lean`

Create this file before section work starts.

Initial imports:

- `import TwoControl.SwapHelpers`

Planned owners:

- `notc`, `notc_conjTranspose`, `notc_mul_notc`, `notc_unitary`, `notc_conj_diag4`
- `bcgate_kron_two`
- `acgate_kron_two`
- `swapab_conj_bcgate_kron_two`
- `swapab_conj_acgate_kron_two`
- `blockify_abgate`
- `blockify_bcgate`
- `blockify_acgate`
- `blockify_controlledGate`
- `controlledGate_unitary`
- `acgate_add`, `bcgate_add`, and any shared gate-addition lemmas
- `acgate_localA_eq`
- `acgate_localC_eq`
- `acgate_localA_commute_bcgate`
- `bcgate_localB_commute_acgate`
- `bcgate_localC_eq`
- `abgate_commute_localC`
- `localC_cancel_right`
- `localC_cancel_left`
- `bcgate_localC_cancel_right`
- `bcgate_localC_cancel_left`
- `bcgate_localC_conj_kron`
- `controlledGate_conj_local_target`
- `ccu_conj_local_target`
- `conj_local_target_twoQubitGate`
- `conj_local_target_product_four`
- `swapab_twoQubitGate`
- `swapac_twoQubitGate`

### `StateHelpers.lean`

Create this file before section work starts.

Initial imports:

- `import Mathlib.LinearAlgebra.Matrix.Vec`
- `import TwoControl.GateHelpers`

Planned owners:

- `ketPlus`
- `detVec2`, `detVec4`
- `colMatrix`
- `qubitPerp`
- all generic `isQubit_*` transport lemmas
- all generic `isProductState_*` and `isEntangled_*` transport lemmas
- all generic `kronVec_*` application, associativity, and cancellation lemmas
- all generic vector normalization lemmas such as `normalize_vec2` and `sumSq_ne_zero_of_ne_zero`
- `mulVec_ne_zero_of_unitary`
- `dot_mulVec_of_unitary`
- `colMatrix_mulVec`
- `colMatrix_unitary_of_orthonormal`
- `qubitPerp_orthogonal`
- `qubit_basis_unitary`

Do not move Section 6 case-analysis lemmas or the controlled-on-first/controlled-on-second characterization steps here.

## Root Import Plan

Required changes before section work:

- no required change to `TwoControl/Main.lean`
- no required change to `TwoControl.lean`

Reason:

- once the new helper files are imported from the section files, they are built transitively.
- helper files only need to be added to `TwoControl/Main.lean` later if a flatter public import surface is desired.

## Exact Checklist By File

### `Prelude.lean`

- no refactor planned
- no import changes planned

### `Definitions.lean`

- no refactor planned
- no import changes planned

### `BlockHelpers.lean`

Import changes:

- none planned in the first pass

Declarations to receive first:

- `finProd_assoc_222` from `Section3.lean`
- `proj0_add_proj1` from the earliest section where it is first duplicated
- `block_one_eq`, `block_diagonal_unitary`, `fromBlocks_diagonal_unitary` from `Section3.lean`

Declarations planned to receive later:

- `upper_block_zero_of_unitary` from `Section6.lean`
- reused `finProdFinEquiv_*` constants from `Section3.lean`, `Section4.lean`, `Section6.lean`, or `Section7.lean` when they are shared rather than section-specific

### `DiagonalizationHelpers.lean`

Import changes:

- none planned in the first pass

Declarations to receive first:

- `diag2_same_eq_smul_one` from `Section3.lean`
- `diag4_unitary` from `Section3.lean`
- `diag4_repeat_norms_of_mem_unitaryGroup` from `Section3.lean`
- `one_kron_diag2` from `Section3.lean`
- `det_diag2` and `det_of_unitary_diag2_decomp` from `Section3.lean`

Declarations planned to receive later:

- `diag2_one_right_kron` from `Section5.lean`
- any later local copies of the same diagonal/unitary transport lemmas from `Section4.lean` and `Section7.lean`

### `KronHelpers.lean`

Create this file before starting `Section3.lean`.

Header to add:

- `import TwoControl.DiagonalizationHelpers`

Declarations to receive first:

- `kron_one_assoc` from `Section3.lean`
- `kron_smul_right` from `Section3.lean`

Declarations planned to receive later:

- `kron_add_right` from `Section4.lean`
- `kron_mul_reindex_local` from `Section4.lean`
- `kron_assoc_222_local` from `Section4.lean`
- `split_one_kron_terms` from `Section4.lean`
- `eq_zero_of_one_kron_eq_zero` from `Section4.lean`
- `conjTranspose_kron_reindex` from `Section4.lean`
- `conjTranspose_kron_reindex_local` from `Section6.lean`

### `SwapHelpers.lean`

Create this file before starting `Section3.lean`.

Header to add:

- `import TwoControl.KronHelpers`

Declarations to receive first:

- `swap2_conjTranspose` from `Section3.lean`
- `swap2_mul_swap2` from `Section3.lean`
- `swap2_unitary` from `Section3.lean`
- `swap2_conj_diag4` from `Section3.lean`

Declarations planned to receive later:

- `swap_index_prod`, `swap2_left_mul_apply`, `swap2_right_mul_apply`, `swap2_conj_apply` from `Section4.lean`
- `swap2_conj_kron_right_local`, `swap2_conj_kron_left_local`, `swap2_conj_kron_local` from `Section4.lean`
- `swapab_mul_swapab` from `Section4.lean`
- `swap2_mulVec_kronVec`, `swapbc_mul_swapbc` from `Section6.lean`
- `swapac`, `swapac_mul_swapac`, `swapab_conj_kron_three`, `swapbc_conj_kron` from `Section7.lean`

### `GateHelpers.lean`

Create this file before starting `Section3.lean`.

Header to add:

- `import TwoControl.SwapHelpers`

Declarations to receive first:

- `notc`, `notc_conjTranspose`, `notc_mul_notc`, `notc_unitary`, `notc_conj_diag4` from `Section3.lean`

Declarations planned to receive later:

- `unitary_column0_norm`, `unitary_column1_norm`, `unitary_columns_orthogonal_left`, `unitary_columns_orthogonal_right`, `unitary_column_projector_sum` from `Section4.lean`
- `ketbra_mulVec`, `ketbra_self_mulVec_of_dotProduct_eq_one`, `ketbra_orthogonal_mulVec`, `ketbra_eq_proj1_of_first_zero`, `ketbra_eq_proj0_of_second_zero` from `Section4.lean`
- `bcgate_kron_two`, `acgate_kron_two`, `swapab_conj_bcgate_kron_two`, `swapab_conj_acgate_kron_two` from `Section4.lean`
- `blockify_bcgate`, `blockify_acgate`, `controlledGate_unitary` from `Section4.lean`
- `blockify_abgate`, `blockify_controlledGate` from `Section5.lean`
- `acgate_localA_eq`, `acgate_localC_eq`, `acgate_localA_commute_bcgate`, `bcgate_localB_commute_acgate`, `swapbc_mulVec_kronVec`, `bcgate_mulVec_kronVec`, `acgate_mulVec_kronVec`, `acgate_mulVec_of_product` from `Section6.lean`
- `bcgate_localC_eq`, `abgate_commute_localC`, `localC_cancel_right`, `localC_cancel_left`, `bcgate_localC_cancel_right`, `bcgate_localC_cancel_left`, `bcgate_localC_conj_kron`, `controlledGate_conj_local_target`, `ccu_conj_local_target`, `conj_local_target_twoQubitGate`, `conj_local_target_product_four`, `swapab_twoQubitGate`, `swapac_twoQubitGate` from `Section7.lean`

### `StateHelpers.lean`

Create this file before starting `Section3.lean`.

Header to add:

- `import Mathlib.LinearAlgebra.Matrix.Vec`
- `import TwoControl.GateHelpers`

Declarations planned to receive later:

- the generic state-space vocabulary and transport lemmas from `Section6.lean`

No declarations move here during the `Section3.lean` pass, but the file should already exist before that pass starts.

### `Section3.lean`

Imports to add before moving anything:

- `import TwoControl.KronHelpers`
- `import TwoControl.SwapHelpers`
- `import TwoControl.GateHelpers`

Keep existing imports initially.

First declarations to move out:

- to `BlockHelpers.lean`: `finProd_assoc_222`, `block_one_eq`, `block_diagonal_unitary`, `fromBlocks_diagonal_unitary`
- to `DiagonalizationHelpers.lean`: `diag2_same_eq_smul_one`, `diag4_unitary`, `diag4_repeat_norms_of_mem_unitaryGroup`, `one_kron_diag2`, `det_diag2`, `det_of_unitary_diag2_decomp`
- to `KronHelpers.lean`: `kron_one_assoc`, `kron_smul_right`
- to `SwapHelpers.lean`: `swap2_conjTranspose`, `swap2_mul_swap2`, `swap2_unitary`, `swap2_conj_diag4`
- to `GateHelpers.lean`: `notc`, `notc_conjTranspose`, `notc_mul_notc`, `notc_unitary`, `notc_conj_diag4`

Declarations to keep local in `Section3.lean`:

- `blockify_W`, `block_scalar_eq`, `smul_eq_smul_implies_zero`
- `tensor_witness_of_eq`, `tensor_witness_of_mul_eq_one`, `eq_or_mul_eq_one_of_three_multiset`
- `one_kron_mul_controlledGate_diag2`, `blockify_diag4`, `repeated_pair_complement`
- `cnot`, `cnot_conjTranspose`, `cnot_mul_cnot`, `cnot_unitary`, `cnot_conj_diag4`
- the three public section lemmas

Exit criterion for the `Section3.lean` pass:

- no generic block, diagonal, Kronecker, swap, or shared fixed-gate helper remains private in `Section3.lean`

### `Section4.lean`

Imports to add before moving anything:

- `import TwoControl.KronHelpers`
- `import TwoControl.SwapHelpers`
- `import TwoControl.GateHelpers`

Keep existing imports initially.

Declarations that should disappear from `Section4.lean` because they were already extracted during the `Section3.lean` pass:

- `finProd_assoc_222`
- `block_one_eq`
- `fromBlocks_diagonal_unitary`
- `block_diagonal_unitary`
- `diag4_unitary`
- `diag4_repeat_norms_of_mem_unitaryGroup`

New declarations to move out during the `Section4.lean` pass:

- to `KronHelpers.lean`: `kron_add_right`, `kron_mul_reindex_local`, `kron_assoc_222_local`, `split_one_kron_terms`, `eq_zero_of_one_kron_eq_zero`, `conjTranspose_kron_reindex`
- to `SwapHelpers.lean`: `swap_index_prod`, `swap2_left_mul_apply`, `swap2_right_mul_apply`, `swap2_conj_apply`, `swap2_conj_kron_right_local`, `swap2_conj_kron_left_local`, `swap2_conj_kron_local`, `swapab_mul_swapab`
- to `GateHelpers.lean`: `unitary_column0_norm`, `unitary_column1_norm`, `unitary_columns_orthogonal_left`, `unitary_columns_orthogonal_right`, `unitary_column_projector_sum`, `ketbra_mulVec`, `ketbra_self_mulVec_of_dotProduct_eq_one`, `ketbra_orthogonal_mulVec`, `ketbra_eq_proj1_of_first_zero`, `ketbra_eq_proj0_of_second_zero`, `bcgate_kron_two`, `acgate_kron_two`, `swapab_conj_bcgate_kron_two`, `swapab_conj_acgate_kron_two`, `blockify_bcgate`, `blockify_acgate`, `controlledGate_unitary`, `swapab_conj_acgate`, `swapab_conj_bcgate`

Declarations to keep local in `Section4.lean`:

- `diag4_one`, `controlledGate_diag2_one`, `ccu_diag2_one`
- `finProd_assoc_11`, `ccu_diag2_last_zero_block`, `ccu_diag2_last_one_block`, `ccu_diag2_11_block`
- `swapab_conj_word_acbc`, `swapab_conj_word_bcac`, `swapab_conj_ccu_diag2`
- the four public section lemmas

Exit criterion for the `Section4.lean` pass:

- no shared gate-transport or gate-blockification helper remains private in `Section4.lean`

### `Section5.lean`

Imports to add before moving anything:

- `import TwoControl.KronHelpers`
- `import TwoControl.SwapHelpers`
- `import TwoControl.GateHelpers`

Keep `import TwoControl.Section4`.

Declarations that should disappear from `Section5.lean` because they already belong to helper modules:

- `finProd_assoc_222`
- `kron_one_assoc`
- `proj0_add_proj1`
- `block_one_eq`
- `kron_add_right`
- `kron_smul_right`
- `kron_mul_reindex_local`
- `kron_assoc_222_local`
- `swap_index_prod`
- `swap2_left_mul_apply`
- `swap2_right_mul_apply`
- `swap2_conj_apply`
- `swap2_conj_kron_right_local`
- `acgate_kron_two`
- `block_diagonal_unitary`
- `fromBlocks_diagonal_unitary`
- `controlledGate_unitary`
- `diag4_unitary`
- `notc`, `notc_conjTranspose`, `notc_mul_notc`, `notc_unitary`, `notc_conj_diag4`

New declarations to move out during the `Section5.lean` pass:

- to `GateHelpers.lean`: `blockify_abgate`, `blockify_controlledGate`
- to `DiagonalizationHelpers.lean`: `diag2_one_right_kron`

Declarations to keep local in `Section5.lean`:

- `nonzero_of_unitary`, `exists_nonzero_entry_of_ne_zero`, `eq_zero_of_kron_right_entry_ne_zero`
- `scalar_of_kron_sum_zero`, `tensor_decomp_of_offdiag_zero`, `unitary_factors_of_kron_unitary`
- `unit_vector_extends_to_unitary`, `eq_witness_of_eq`, `prod_one_witness`
- the public section lemma

Exit criterion for the `Section5.lean` pass:

- `Section5.lean` contains tensor-decomposition proof machinery, but not reused Kronecker/swap/gate helpers

### `Section6.lean`

Imports to add before moving anything:

- `import TwoControl.KronHelpers`
- `import TwoControl.SwapHelpers`
- `import TwoControl.GateHelpers`
- `import TwoControl.StateHelpers`

Keep `import Mathlib.LinearAlgebra.Matrix.Vec` and `import TwoControl.Section5`.

Declarations that should disappear from `Section6.lean` because they already belong to helper modules:

- all repeated Kronecker, swap, block, and gate helpers already assigned above

New declarations to move out during the `Section6.lean` pass:

- to `StateHelpers.lean`: `ketPlus`, `detVec2`, `detVec4`, `colMatrix`, `qubitPerp`, all generic `isQubit_*`, `isProductState_*`, `isEntangled_*`, generic `kronVec_*`, normalization, basis, and `mulVec` transport lemmas
- to `SwapHelpers.lean`: `swap2_mulVec_kronVec`, `swapbc_mul_swapbc`, `swapab_mulVec_kronVec`
- to `GateHelpers.lean`: `acgate_localA_eq`, `acgate_localC_eq`, `acgate_localA_commute_bcgate`, `bcgate_localB_commute_acgate`, `swapbc_mulVec_kronVec`, `bcgate_mulVec_kronVec`, `acgate_mulVec_kronVec`, `acgate_mulVec_of_product`
- to `BlockHelpers.lean`: `upper_block_zero_of_unitary`
- to `KronHelpers.lean`: `conjTranspose_kron_reindex_local`

Declarations to keep local in `Section6.lean`:

- `exists_product_state_on_left_ket0`
- the controlled-on-first and controlled-on-second characterization lemmas
- theorem-case helpers such as `section6_lemma_6_2_branchB`, `section6_lemma_6_2_caseC`, `section6_lemma_6_2_caseA`, `section6_lemma_6_3_normalize_V₂`, `section6_lemma_6_3_identity_transfer`
- the four public section lemmas

Exit criterion for the `Section6.lean` pass:

- all general state-space lemmas live in `StateHelpers.lean`; only Section 6 proof logic stays local

### `Section7.lean`

Imports to add before moving anything:

- `import TwoControl.KronHelpers`
- `import TwoControl.SwapHelpers`
- `import TwoControl.GateHelpers`

Keep `import TwoControl.Section6`.

Declarations that should disappear from `Section7.lean` because they already belong to helper modules:

- repeated `diag4_unitary`
- repeated Kronecker helpers
- repeated swap helpers
- repeated embedded-gate helpers

New declarations to move out during the `Section7.lean` pass:

- to `SwapHelpers.lean`: `swapac`, `swapac_mul_swapac`, `swapab_conj_kron_three`, `swapbc_conj_kron`, `swap2_conj_unitary`
- to `GateHelpers.lean`: `bcgate_localC_eq`, `abgate_commute_localC`, `acgate_localC_eq`, `localC_cancel_right`, `localC_cancel_left`, `bcgate_localC_cancel_right`, `bcgate_localC_cancel_left`, `bcgate_localC_conj_kron`, `controlledGate_conj_local_target`, `ccu_conj_local_target`, `conj_local_target_twoQubitGate`, `conj_local_target_product_four`, `swapab_twoQubitGate`, `swapac_twoQubitGate`, and the reusable swap-conjugation lemmas for `abgate`/`bcgate`/`acgate`
- to `DiagonalizationHelpers.lean`: replace `det_of_unitary_diag2_decomp_local` with the shared `det_of_unitary_diag2_decomp`

Declarations to keep local in `Section7.lean`:

- `diag8`, `ccu_diag2_eq`, `abgate_controlledGate_diag2_eq`, `abgate_controlled_mul_ccu`, `section7_lemma_7_1_left`, `ccu_mul_abgate_controlled`, `section7_lemma_7_1_right`
- `swapbc_conj_mul2`, `swapbc_conj_ccu_diag2_one`, `swapac_conj_ccu_diag2_one`, `swap2_conj_diag4_one`
- `canonicalPair_first_norm`, `canonicalPair_step`
- `swapbc_conj_word_acab`, `normalize_word_acabac`, `normalize_word_acbcab`, `normalize_word_bcabac`, `swapbc_conj_word_abacbc`, `swapbc_conj_word_abacabbc`, `swapbc_conj_word_abbabbc`, `swapbc_conj_word_abbcacbc`, `section7_lemma_7_2_step3`
- the public Section 7 lemmas, theorem, and corollary

Exit criterion for the `Section7.lean` pass:

- `Section7.lean` contains canonical-form proof logic and final results, but not reusable swap/gate transport infrastructure

## Execution Order

Use this order.

1. create `KronHelpers.lean`, `SwapHelpers.lean`, `GateHelpers.lean`, and `StateHelpers.lean` with their headers and section comments only
2. update the section-file headers to import the helper files they will depend on
3. perform the full `Section3.lean` extraction pass and stop only when its exit criterion is met
4. perform the full `Section4.lean` extraction pass and stop only when its exit criterion is met
5. continue the same way through `Section7.lean`

This is the intended workflow:

- helper ownership is fixed globally before the first proof file is touched
- proof cleanup is completed section by section
- no section is left half-converted before moving to the next one

## Working Rule Going Forward

When a new declaration is added, place it by answering two questions.

1. Would this declaration still make sense if the paper had no Section 3-7 numbering?
   If yes, it is not a proof step.
2. Is this declaration already useful in a second section file?
   If yes, it does not belong in a section file.

That rule is enough to keep the interface layer, helper layer, and proof layer separated.