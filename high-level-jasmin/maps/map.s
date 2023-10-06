	.att_syntax
	.text
	.p2align	5
	.globl	_test_map_optimized_u64
	.globl	test_map_optimized_u64
	.globl	_test_map_simple_u64
	.globl	test_map_simple_u64
_test_map_optimized_u64:
test_map_optimized_u64:
	movq	%rsp, %r10
	leaq	-128(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rsp, %rax
	movq	$0, %rcx
	jmp 	Ltest_map_optimized_u64$5
Ltest_map_optimized_u64$6:
	movq	(%rdi,%rcx,8), %rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
Ltest_map_optimized_u64$5:
	cmpq	$16, %rcx
	jb  	Ltest_map_optimized_u64$6
	movq	%rsp, %rax
	movq	$0, %rcx
	jmp 	Ltest_map_optimized_u64$3
Ltest_map_optimized_u64$4:
	movq	(%rax,%rcx,8), %rdx
	incq	%rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
	movq	(%rax,%rcx,8), %rdx
	incq	%rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
	movq	(%rax,%rcx,8), %rdx
	incq	%rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
	movq	(%rax,%rcx,8), %rdx
	incq	%rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
Ltest_map_optimized_u64$3:
	cmpq	$16, %rcx
	jb  	Ltest_map_optimized_u64$4
	movq	%rsp, %rax
	movq	$0, %rcx
	jmp 	Ltest_map_optimized_u64$1
Ltest_map_optimized_u64$2:
	movq	(%rax,%rcx,8), %rdx
	movq	%rdx, (%rdi,%rcx,8)
	incq	%rcx
Ltest_map_optimized_u64$1:
	cmpq	$16, %rcx
	jb  	Ltest_map_optimized_u64$2
	movq	%r10, %rsp
	ret
_test_map_simple_u64:
test_map_simple_u64:
	movq	%rsp, %r10
	leaq	-128(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rsp, %rax
	movq	$0, %rcx
	jmp 	Ltest_map_simple_u64$5
Ltest_map_simple_u64$6:
	movq	(%rdi,%rcx,8), %rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
Ltest_map_simple_u64$5:
	cmpq	$16, %rcx
	jb  	Ltest_map_simple_u64$6
	movq	%rsp, %rax
	movq	$0, %rcx
	jmp 	Ltest_map_simple_u64$3
Ltest_map_simple_u64$4:
	movq	(%rax,%rcx,8), %rdx
	incq	%rdx
	movq	%rdx, (%rax,%rcx,8)
	incq	%rcx
Ltest_map_simple_u64$3:
	cmpq	$16, %rcx
	jb  	Ltest_map_simple_u64$4
	movq	%rsp, %rax
	movq	$0, %rcx
	jmp 	Ltest_map_simple_u64$1
Ltest_map_simple_u64$2:
	movq	(%rax,%rcx,8), %rdx
	movq	%rdx, (%rdi,%rcx,8)
	incq	%rcx
Ltest_map_simple_u64$1:
	cmpq	$16, %rcx
	jb  	Ltest_map_simple_u64$2
	movq	%r10, %rsp
	ret
