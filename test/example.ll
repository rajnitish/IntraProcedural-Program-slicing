; ModuleID = 'example.c'
source_filename = "example.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [3 x i8] c"%d\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  store i32 6, i32* %2, align 4
  store i32 2, i32* %3, align 4
  store i32 3, i32* %4, align 4
  store i32 3, i32* %5, align 4
  store i32 5, i32* %6, align 4
  br label %7

; <label>:7:                                      ; preds = %21, %0
  %8 = load i32, i32* %2, align 4
  %9 = load i32, i32* %6, align 4
  %10 = icmp ne i32 %8, %9
  br i1 %10, label %11, label %22

; <label>:11:                                     ; preds = %7
  %12 = load i32, i32* %2, align 4
  %13 = icmp sgt i32 %12, 2
  br i1 %13, label %14, label %17

; <label>:14:                                     ; preds = %11
  %15 = load i32, i32* %3, align 4
  %16 = add nsw i32 %15, 1
  store i32 %16, i32* %5, align 4
  br label %21

; <label>:17:                                     ; preds = %11
  %18 = load i32, i32* %3, align 4
  %19 = load i32, i32* %5, align 4
  %20 = add nsw i32 %18, %19
  store i32 %20, i32* %6, align 4
  br label %21

; <label>:21:                                     ; preds = %17, %14
  br label %7

; <label>:22:                                     ; preds = %7
  %23 = load i32, i32* %5, align 4
  %24 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i32 0, i32 0), i32 %23)
  %25 = load i32, i32* %6, align 4
  %26 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i32 0, i32 0), i32 %25)
  ret i32 0
}

declare i32 @printf(i8*, ...) #1

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
